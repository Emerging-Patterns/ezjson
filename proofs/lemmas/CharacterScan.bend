# the character scan between and inside tokens: escapes, hex digits, words
import Base
import ../../src/lex.bend as Lex
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ../../laws/defs/GrammarDerivations.bend as D2
import ./ArrayLength.bend as M1
import ./CharacterClasses.bend as M2
import ./LexemeOrder.bend as M3
import ./LexerPunctuation.bend as M4
import ./NumberCharsAreWordChars.bend as M5
import ./StringTokens.bend as M6
import ./WellFormedCells.bend as M7
import ./WordLexing.bend as M8

# laws/EscapesDecode.bend: escapes

# whether a Maybe of a character is None
def is_nonec(mb: Maybe<&2, Char>) -> Bool:
  match mb:
    case None{}:
      True{}
    case Some{_ch}:
      False{}

# the character after a backslash, when it is a two-character escape
law esc_to:
  for isu: Bool
  for +uu: U32
  for +cc: Char
  for +bf: List<&2, Char>
  for eu: {U32.is_eq(uu, 117) == isu : Bool}
  for h_e: {D2.unesc(Chr{uu}) == Some{cc} : Maybe<&2, Char>}
  {Lex.escape.go(Chr{uu}, bf, [], isu) == Lex.Lex{Lex.Str{}, cc <> bf, []} : Lex.Lex}

def esc_to(isu, uu, cc, bf, eu, h_e):
  match isu:
    case True{}:
      ek = Equal.sym(U32, uu, 117, M7.ueq(uu, 117, eu))
      e2 = Equal.trans(Maybe<&2, Char>, D2.unesc(Chr{117}), D2.unesc(Chr{uu}), Some{cc},
        Equal.cong(U32, Maybe<&2, Char>, zz => D2.unesc(Chr{zz}), 117, uu, ek), h_e)
      Empty.absurd({Lex.escape.go(Chr{uu}, bf, [], True{}) == Lex.Lex{Lex.Str{}, cc <> bf, []} : Lex.Lex},
        M1.true_false(Equal.cong(Maybe<&2, Char>, Bool, zz => is_nonec(zz), None{}, Some{cc}, e2)))
    case False{}:
      es = Equal.sym(Maybe<&2, Char>, D2.unesc(Chr{uu}), Some{cc}, h_e)
      %es : {Lex.escape.put(_, bf, []) == Lex.Lex{Lex.Str{}, cc <> bf, []} : Lex.Lex}
      {==}

# laws/EscapesDecode.bend: \u escapes

# a hex digit of a \u escape
law uni_step:
  for left: Nat
  for +acc: U32
  for +ch: Char
  for +bf: List<&2, Char>
  for h: {D2.hexd(ch) == True{} : Bool}
  {Lex.feed(ch, Lex.Lex{Lex.Uni{left, acc}, bf, []}) == Lex.unicode.put(left, acc, Lex.hex(ch), bf, []) : Lex.Lex}

def uni_step(left, acc, ch, bf, h):
  hs = Equal.sym(Bool, D2.hexd(ch), True{}, h)
  %hs : {Lex.unicode.go(left, acc, ch, bf, [], _) == Lex.unicode.put(left, acc, Lex.hex(ch), bf, []) : Lex.Lex}
  {==}

# a hex digit of a low surrogate's \u escape
law low_step:
  for left: Nat
  for +acc: U32
  for +hi: U32
  for +ch: Char
  for +bf: List<&2, Char>
  for h: {D2.hexd(ch) == True{} : Bool}
  {Lex.feed(ch, Lex.Lex{Lex.Lo{left, acc, hi}, bf, []}) == Lex.unicode.low.put(left, acc, hi, Lex.hex(ch), bf,
    []) : Lex.Lex}

def low_step(left, acc, hi, ch, bf, h):
  hs = Equal.sym(Bool, D2.hexd(ch), True{}, h)
  %hs : {Lex.unicode.low.go(left, acc, hi, ch, bf, [], _) == Lex.unicode.low.put(left, acc, hi, Lex.hex(ch), bf,
    []) : Lex.Lex}
  {==}

# the last test of sur_ok
law sur_ok.lo2:
  for g2: Bool
  for l2: Bool
  for h: {Bool.not(Bool.and(g2, l2)) == True{} : Bool}
  {Lex.unicode.sur.lo(g2, l2) == Lex.SOk{} : Lex.Sur}

def sur_ok.lo2(g2, l2, h):
  match g2:
    case True{}:
      match l2:
        case True{}:
          M3.no({Lex.unicode.sur.lo(True{}, True{}) == Lex.SOk{} : Lex.Sur}, h)
        case False{}:
          {==}
    case False{}:
      {==}

# the low half of sur_ok.go
law sur_ok.lo:
  for g2: Bool
  for l2: Bool
  for +cp: U32
  for e3: {U32.is_ge(cp, 56320) == g2 : Bool}
  for e4: {U32.is_le(cp, 57343) == l2 : Bool}
  for h: {Bool.not(Bool.and(g2, l2)) == True{} : Bool}
  {Lex.unicode.sur.lo(U32.is_ge(cp, 56320), U32.is_le(cp, 57343)) == Lex.SOk{} : Lex.Sur}

def sur_ok.lo(g2, l2, cp, e3, e4, h):
  s3 = Equal.sym(Bool, U32.is_ge(cp, 56320), g2, e3)
  s4 = Equal.sym(Bool, U32.is_le(cp, 57343), l2, e4)
  %s3 : {Lex.unicode.sur.lo(_, U32.is_le(cp, 57343)) == Lex.SOk{} : Lex.Sur}
  %s4 : {Lex.unicode.sur.lo(g2, _) == Lex.SOk{} : Lex.Sur}
  sur_ok.lo2(g2, l2, h)

# a code point that is no surrogate, with its range tests named
law sur_ok.go:
  for g1: Bool
  for l1: Bool
  for g2: Bool
  for l2: Bool
  for +cp: U32
  for e3: {U32.is_ge(cp, 56320) == g2 : Bool}
  for e4: {U32.is_le(cp, 57343) == l2 : Bool}
  for h: {Bool.and(Bool.not(Bool.and(g1, l1)), Bool.not(Bool.and(g2, l2))) == True{} : Bool}
  {Lex.unicode.sur.hi(cp, g1, l1) == Lex.SOk{} : Lex.Sur}

def sur_ok.go(g1, l1, g2, l2, cp, e3, e4, h):
  match g1:
    case True{}:
      match l1:
        case True{}:
          M3.no({Lex.unicode.sur.hi(cp, True{}, True{}) == Lex.SOk{} : Lex.Sur}, h)
        case False{}:
          sur_ok.lo(g2, l2, cp, e3, e4, h)
    case False{}:
      sur_ok.lo(g2, l2, cp, e3, e4, h)

# a code point that is no surrogate is an ordinary \u escape
law sur_ok:
  for +cp: U32
  for h: {D2.non_sur(cp) == True{} : Bool}
  {Lex.unicode.sur(cp) == Lex.SOk{} : Lex.Sur}

def sur_ok(cp, h):
  sur_ok.go(U32.is_ge(cp, 55296), U32.is_le(cp, 56319), U32.is_ge(cp, 56320), U32.is_le(cp, 57343), cp, {==}, {==}, h)

# a high surrogate, with its range tests named
law sur_hi.go:
  for g1: Bool
  for l1: Bool
  for +cp: U32
  for h: {Bool.and(g1, l1) == True{} : Bool}
  {Lex.unicode.sur.hi(cp, g1, l1) == Lex.SHi{} : Lex.Sur}

def sur_hi.go(g1, l1, cp, h):
  match g1:
    case True{}:
      match l1:
        case True{}:
          {==}
        case False{}:
          M3.no({Lex.unicode.sur.hi(cp, True{}, False{}) == Lex.SHi{} : Lex.Sur}, h)
    case False{}:
      M3.no({Lex.unicode.sur.hi(cp, False{}, l1) == Lex.SHi{} : Lex.Sur}, h)

# a high surrogate's \u escape waits for its pair
law sur_hi:
  for +cp: U32
  for h: {D2.in_hi(cp) == True{} : Bool}
  {Lex.unicode.sur(cp) == Lex.SHi{} : Lex.Sur}

def sur_hi(cp, h):
  sur_hi.go(U32.is_ge(cp, 55296), U32.is_le(cp, 56319), cp, h)

# a low surrogate, the low half
law sur_lo.lo:
  for g2: Bool
  for l2: Bool
  for h: {Bool.and(g2, l2) == True{} : Bool}
  {Lex.unicode.sur.lo(g2, l2) == Lex.SLo{} : Lex.Sur}

def sur_lo.lo(g2, l2, h):
  match g2:
    case True{}:
      match l2:
        case True{}:
          {==}
        case False{}:
          M3.no({Lex.unicode.sur.lo(True{}, False{}) == Lex.SLo{} : Lex.Sur}, h)
    case False{}:
      M3.no({Lex.unicode.sur.lo(False{}, l2) == Lex.SLo{} : Lex.Sur}, h)

# a low surrogate, with its range tests named
law sur_lo.go:
  for g1: Bool
  for l1: Bool
  for +cp: U32
  for h: {Bool.and(Bool.not(Bool.and(g1, l1)), D2.in_lo(cp)) == True{} : Bool}
  {Lex.unicode.sur.hi(cp, g1, l1) == Lex.SLo{} : Lex.Sur}

def sur_lo.go(g1, l1, cp, h):
  match g1:
    case True{}:
      match l1:
        case True{}:
          M3.no({Lex.unicode.sur.hi(cp, True{}, True{}) == Lex.SLo{} : Lex.Sur}, h)
        case False{}:
          sur_lo.lo(U32.is_ge(cp, 56320), U32.is_le(cp, 57343), M3.and_right(True{}, D2.in_lo(cp), h))
    case False{}:
      sur_lo.lo(U32.is_ge(cp, 56320), U32.is_le(cp, 57343), M3.and_right(True{}, D2.in_lo(cp), h))

# a low surrogate's \u escape
law sur_lo:
  for +cp: U32
  for h: {D2.lo_sur(cp) == True{} : Bool}
  {Lex.unicode.sur(cp) == Lex.SLo{} : Lex.Sur}

def sur_lo(cp, h):
  sur_lo.go(U32.is_ge(cp, 55296), U32.is_le(cp, 56319), cp, h)

# four hex digits of a \u escape
law u4_feed:
  for +aa: Char
  for +bb: Char
  for +cc: Char
  for +dd: Char
  for +bf: List<&2, Char>
  for ha: {D2.hexd(aa) == True{} : Bool}
  for hb: {D2.hexd(bb) == True{} : Bool}
  for hc: {D2.hexd(cc) == True{} : Bool}
  for hd: {D2.hexd(dd) == True{} : Bool}
  {Lex.feed(dd, Lex.feed(cc, Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Uni{3n, 0}, bf, []})))) ==
    Lex.unicode.end(D2.hex4(aa, bb, cc, dd), bf, []) : Lex.Lex}

def u4_feed(aa, bb, cc, dd, bf, ha, hb, hc, hd):
  Equal.trans(Lex.Lex, Lex.feed(dd, Lex.feed(cc, Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Uni{3n, 0}, bf, []})))),
    Lex.feed(dd, Lex.Lex{Lex.Uni{0n, D2.hex.acc(D2.hex.acc(D2.hex.acc(0, aa), bb), cc)}, bf, []}),
    Lex.unicode.end(D2.hex4(aa, bb, cc, dd), bf, []),
    Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.feed(dd, zz), Lex.feed(cc, Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Uni{3n, 0},
      bf, []}))), Lex.Lex{Lex.Uni{0n, D2.hex.acc(D2.hex.acc(D2.hex.acc(0, aa), bb), cc)}, bf, []},
      Equal.trans(Lex.Lex, Lex.feed(cc, Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Uni{3n, 0}, bf, []}))), Lex.feed(cc,
      Lex.Lex{Lex.Uni{1n, D2.hex.acc(D2.hex.acc(0, aa), bb)}, bf, []}), Lex.Lex{Lex.Uni{0n,
      D2.hex.acc(D2.hex.acc(D2.hex.acc(0, aa), bb), cc)}, bf, []},
    Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.feed(cc, zz), Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Uni{3n, 0}, bf, []})),
      Lex.Lex{Lex.Uni{1n, D2.hex.acc(D2.hex.acc(0, aa), bb)}, bf, []}, Equal.trans(Lex.Lex, Lex.feed(bb,
      Lex.feed(aa, Lex.Lex{Lex.Uni{3n, 0}, bf, []})), Lex.feed(bb, Lex.Lex{Lex.Uni{2n, D2.hex.acc(0, aa)}, bf, []}),
      Lex.Lex{Lex.Uni{1n, D2.hex.acc(D2.hex.acc(0, aa), bb)}, bf, []},
    Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.feed(bb, zz), Lex.feed(aa, Lex.Lex{Lex.Uni{3n, 0}, bf, []}),
      Lex.Lex{Lex.Uni{2n, D2.hex.acc(0, aa)}, bf, []}, uni_step(3n, 0, aa, bf, ha)),
    uni_step(2n, D2.hex.acc(0, aa), bb, bf, hb))),
    uni_step(1n, D2.hex.acc(D2.hex.acc(0, aa), bb), cc, bf, hc))),
    uni_step(0n, D2.hex.acc(D2.hex.acc(D2.hex.acc(0, aa), bb), cc), dd, bf, hd))

# four hex digits of a low surrogate's \u escape
law l4_feed:
  for +aa: Char
  for +bb: Char
  for +cc: Char
  for +dd: Char
  for +hi: U32
  for +bf: List<&2, Char>
  for ha: {D2.hexd(aa) == True{} : Bool}
  for hb: {D2.hexd(bb) == True{} : Bool}
  for hc: {D2.hexd(cc) == True{} : Bool}
  for hd: {D2.hexd(dd) == True{} : Bool}
  {Lex.feed(dd, Lex.feed(cc, Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Lo{3n, 0, hi}, bf, []})))) ==
    Lex.unicode.low.end(D2.hex4(aa, bb, cc, dd), hi, bf, []) : Lex.Lex}

def l4_feed(aa, bb, cc, dd, hi, bf, ha, hb, hc, hd):
  Equal.trans(Lex.Lex, Lex.feed(dd, Lex.feed(cc, Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Lo{3n, 0, hi}, bf, []})))),
    Lex.feed(dd, Lex.Lex{Lex.Lo{0n, D2.hex.acc(D2.hex.acc(D2.hex.acc(0, aa), bb), cc), hi}, bf, []}),
    Lex.unicode.low.end(D2.hex4(aa, bb, cc, dd), hi, bf, []),
    Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.feed(dd, zz), Lex.feed(cc, Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Lo{3n, 0,
      hi}, bf, []}))), Lex.Lex{Lex.Lo{0n, D2.hex.acc(D2.hex.acc(D2.hex.acc(0, aa), bb), cc), hi}, bf, []},
      Equal.trans(Lex.Lex, Lex.feed(cc, Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Lo{3n, 0, hi}, bf, []}))), Lex.feed(cc,
      Lex.Lex{Lex.Lo{1n, D2.hex.acc(D2.hex.acc(0, aa), bb), hi}, bf, []}), Lex.Lex{Lex.Lo{0n,
      D2.hex.acc(D2.hex.acc(D2.hex.acc(0, aa), bb), cc), hi}, bf, []},
    Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.feed(cc, zz), Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Lo{3n, 0, hi}, bf,
      []})), Lex.Lex{Lex.Lo{1n, D2.hex.acc(D2.hex.acc(0, aa), bb), hi}, bf, []}, Equal.trans(Lex.Lex, Lex.feed(bb,
      Lex.feed(aa, Lex.Lex{Lex.Lo{3n, 0, hi}, bf, []})), Lex.feed(bb, Lex.Lex{Lex.Lo{2n, D2.hex.acc(0, aa), hi}, bf,
      []}), Lex.Lex{Lex.Lo{1n, D2.hex.acc(D2.hex.acc(0, aa), bb), hi}, bf, []},
    Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.feed(bb, zz), Lex.feed(aa, Lex.Lex{Lex.Lo{3n, 0, hi}, bf, []}),
      Lex.Lex{Lex.Lo{2n, D2.hex.acc(0, aa), hi}, bf, []}, low_step(3n, 0, hi, aa, bf, ha)),
    low_step(2n, D2.hex.acc(0, aa), hi, bb, bf, hb))),
    low_step(1n, D2.hex.acc(D2.hex.acc(0, aa), bb), hi, cc, bf, hc))),
    low_step(0n, D2.hex.acc(D2.hex.acc(D2.hex.acc(0, aa), bb), cc), hi, dd, bf, hd))

# four hex digits, from one proof of all four
law and4_1:
  for aa: Bool
  for -bb: Bool
  for -cc: Bool
  for -dd: Bool
  for h: {Bool.and(aa, Bool.and(bb, Bool.and(cc, dd))) == True{} : Bool}
  {aa == True{} : Bool}

def and4_1(aa, bb, cc, dd, h):
  M3.and_left(aa, Bool.and(bb, Bool.and(cc, dd)), h)

law and4_2:
  for aa: Bool
  for bb: Bool
  for -cc: Bool
  for -dd: Bool
  for h: {Bool.and(aa, Bool.and(bb, Bool.and(cc, dd))) == True{} : Bool}
  {bb == True{} : Bool}

def and4_2(aa, bb, cc, dd, h):
  M3.and_left(bb, Bool.and(cc, dd), M3.and_right(aa, Bool.and(bb, Bool.and(cc, dd)), h))

law and4_3:
  for aa: Bool
  for bb: Bool
  for cc: Bool
  for -dd: Bool
  for h: {Bool.and(aa, Bool.and(bb, Bool.and(cc, dd))) == True{} : Bool}
  {cc == True{} : Bool}

def and4_3(aa, bb, cc, dd, h):
  M3.and_left(cc, dd, M3.and_right(bb, Bool.and(cc, dd), M3.and_right(aa, Bool.and(bb, Bool.and(cc, dd)), h)))

law and4_4:
  for aa: Bool
  for bb: Bool
  for cc: Bool
  for dd: Bool
  for h: {Bool.and(aa, Bool.and(bb, Bool.and(cc, dd))) == True{} : Bool}
  {dd == True{} : Bool}

def and4_4(aa, bb, cc, dd, h):
  M3.and_right(cc, dd, M3.and_right(bb, Bool.and(cc, dd), M3.and_right(aa, Bool.and(bb, Bool.and(cc, dd)), h)))

# laws/WhitespaceBetweenTokensIgnored.bend: any other character put between tokens. A scan that every
# text parse accepts passes (sc.acc). Outside strings it keeps how deep the
# text is in brackets and what the last token lets come next: a value (at
# the start, after a comma or a colon), a value or a close (after an open
# bracket), or a comma, a colon or a close (after a value). A word is read
# whole, and must be a literal name or a number when it ends

# what the last token outside strings lets come next
type Lt is Data:
  LSt{}
  LOp{}
  LVal{}

# where the scan is: outside strings, in a word (its characters reversed),
# in a string, just after a backslash in one, or past a fault
type Sc is Data:
  SOut{lt: Lt, dd: Nat}
  SWord{buf: List<&2, Char>, dd: Nat}
  SIn{dd: Nat}
  SEsc{dd: Nat}
  SBad{}

# a close bracket, one level up
def sc.down(dd: Nat) -> Sc:
  match dd:
    case 0n:
      SBad{}
    case 1n+ee:
      SOut{LVal{}, ee}

# an open bracket
def sc.open(lt: Lt, dd: Nat) -> Sc:
  match lt:
    case LSt{}:
      SOut{LOp{}, 1n+dd}
    case LOp{}:
      SOut{LOp{}, 1n+dd}
    case LVal{}:
      SBad{}

# a close bracket
def sc.close(lt: Lt, dd: Nat) -> Sc:
  match lt:
    case LSt{}:
      SBad{}
    case LOp{}:
      sc.down(dd)
    case LVal{}:
      sc.down(dd)

# a comma or a colon
def sc.sep(lt: Lt, dd: Nat) -> Sc:
  match lt:
    case LSt{}:
      SBad{}
    case LOp{}:
      SBad{}
    case LVal{}:
      SOut{LSt{}, dd}

# a punctuation character
def sc.punct(lt: Lt, dd: Nat, tk: Lex.Tok) -> Sc:
  match tk:
    case Lex.TOpenArr{}:
      sc.open(lt, dd)
    case Lex.TCloseArr{}:
      sc.close(lt, dd)
    case Lex.TOpenObj{}:
      sc.open(lt, dd)
    case Lex.TCloseObj{}:
      sc.close(lt, dd)
    case Lex.TColon{}:
      sc.sep(lt, dd)
    case Lex.TComma{}:
      sc.sep(lt, dd)
    case _:
      SBad{}

# a quotation mark outside strings
def sc.quote(lt: Lt, dd: Nat) -> Sc:
  match lt:
    case LSt{}:
      SIn{dd}
    case LOp{}:
      SIn{dd}
    case LVal{}:
      SBad{}

# a word's first character
def sc.wstart(lt: Lt, dd: Nat, ch: Char) -> Sc:
  match lt:
    case LSt{}:
      SWord{[ch], dd}
    case LOp{}:
      SWord{[ch], dd}
    case LVal{}:
      SBad{}

# one character outside strings, by its class
def sc.out(lt: Lt, dd: Nat, cls: Lex.Class, ch: Char) -> Sc:
  match cls:
    case Lex.CPunct{tk}:
      sc.punct(lt, dd, tk)
    case Lex.CQuote{}:
      sc.quote(lt, dd)
    case Lex.CBack{}:
      SBad{}
    case Lex.CSpace{}:
      SOut{lt, dd}
    case Lex.COther{}:
      sc.wstart(lt, dd, ch)

# the end of a word: it must be a literal name or a number
def sc.wend(buf: List<&2, Char>, dd: Nat, cls: Lex.Class, ch: Char) -> Sc:
  Bool.pick(Sc, D1.lit_or_num(Lex.text(buf)), sc.out(LVal{}, dd, cls, ch), SBad{})

# one character in a word
def sc.word(buf: List<&2, Char>, dd: Nat, cls: Lex.Class, ch: Char) -> Sc:
  match cls:
    case Lex.CPunct{tk}:
      sc.wend(buf, dd, Lex.CPunct{tk}, ch)
    case Lex.CQuote{}:
      sc.wend(buf, dd, Lex.CQuote{}, ch)
    case Lex.CBack{}:
      sc.wend(buf, dd, Lex.CBack{}, ch)
    case Lex.CSpace{}:
      sc.wend(buf, dd, Lex.CSpace{}, ch)
    case Lex.COther{}:
      SWord{ch <> buf, dd}

# one character in a string
def sc.in(dd: Nat, cls: Lex.Class) -> Sc:
  match cls:
    case Lex.CPunct{_}:
      SIn{dd}
    case Lex.CQuote{}:
      SOut{LVal{}, dd}
    case Lex.CBack{}:
      SEsc{dd}
    case Lex.CSpace{}:
      SIn{dd}
    case Lex.COther{}:
      SIn{dd}

# one character, its class given
def sc.stepc(st: Sc, cls: Lex.Class, ch: Char) -> Sc:
  match st:
    case SOut{lt, dd}:
      sc.out(lt, dd, cls, ch)
    case SWord{buf, dd}:
      sc.word(buf, dd, cls, ch)
    case SIn{dd}:
      sc.in(dd, cls)
    case SEsc{dd}:
      SIn{dd}
    case SBad{}:
      SBad{}

# one character
def sc.step(st: Sc, +ch: Char) -> Sc:
  sc.stepc(st, Lex.classify(ch), ch)

# every character, in order
def sc.run(txt: String, st: Sc) -> Sc:
  match txt:
    case SNil{}:
      st
    case SCon{hd, tl}:
      sc.run(tl, sc.step(st, hd))

# the scan at the end of the text: a word there ends
def sc.fin(st: Sc) -> Sc:
  match st:
    case SOut{lt, dd}:
      SOut{lt, dd}
    case SWord{buf, dd}:
      Bool.pick(Sc, D1.lit_or_num(Lex.text(buf)), SOut{LVal{}, dd}, SBad{})
    case SIn{dd}:
      SIn{dd}
    case SEsc{dd}:
      SEsc{dd}
    case SBad{}:
      SBad{}

# after a value, at the top level
def sc.top.o(lt: Lt, dd: Nat) -> Bool:
  match lt:
    case LVal{}:
      match dd:
        case 0n:
          True{}
        case 1n+_:
          False{}
    case _:
      False{}

def sc.top(st: Sc) -> Bool:
  match st:
    case SOut{lt, dd}:
      sc.top.o(lt, dd)
    case _:
      False{}

# whether the scan accepts, once the text is over
def sc.acc(st: Sc) -> Bool:
  sc.top(sc.fin(st))

# a word character's class
def is_oth(cls: Lex.Class) -> Bool:
  match cls:
    case Lex.COther{}:
      True{}
    case _:
      False{}

# what may come next is not a separator or a close
def notval(lt: Lt) -> Bool:
  match lt:
    case LVal{}:
      False{}
    case _:
      True{}

# what a derivation of a kind starts after: a value after anything but a
# value, cells after a value
def okl(kk: D2.GK, lt: Lt) -> Bool:
  match kk:
    case D2.GKVal{}:
      notval(lt)
    case _:
      Bool.not(notval(lt))

# the scan over two texts, one after the other
law sc_app:
  for +aa: String
  for +bb: String
  for +st: Sc
  {sc.run(aa ++ bb, st) == sc.run(bb, sc.run(aa, st)) : Sc}

def sc_app(aa, bb, st):
  match aa:
    case SNil{}:
      {==}
    case SCon{+hd, +tl}:
      sc_app(tl, bb, sc.step(st, hd))

# a word's end, by whether it is a literal name or a number
law pick_step:
  for bv: Bool
  for +dd: Nat
  for +cls: Lex.Class
  for +ch: Char
  {Bool.pick(Sc, bv, sc.out(LVal{}, dd, cls, ch), SBad{}) == sc.stepc(Bool.pick(Sc, bv, SOut{LVal{}, dd}, SBad{}),
    cls, ch) : Sc}

def pick_step(bv, _dd, _cls, _ch):
  match bv:
    case True{}:
      {==}
    case False{}:
      {==}

# a character that is no word character ends a word as the end of the text
# does
law fin_stepc:
  for +st: Sc
  for +cls: Lex.Class
  for +ch: Char
  for h: {is_oth(cls) == False{} : Bool}
  {sc.stepc(st, cls, ch) == sc.stepc(sc.fin(st), cls, ch) : Sc}

def fin_stepc(st, cls, ch, h):
  match st:
    case SOut{_lt, _dd}:
      {==}
    case SWord{+buf, +dd}:
      match cls:
        case Lex.CPunct{+tk}:
          pick_step(D1.lit_or_num(Lex.text(buf)), dd, Lex.CPunct{tk}, ch)
        case Lex.CQuote{}:
          pick_step(D1.lit_or_num(Lex.text(buf)), dd, Lex.CQuote{}, ch)
        case Lex.CBack{}:
          pick_step(D1.lit_or_num(Lex.text(buf)), dd, Lex.CBack{}, ch)
        case Lex.CSpace{}:
          pick_step(D1.lit_or_num(Lex.text(buf)), dd, Lex.CSpace{}, ch)
        case Lex.COther{}:
          Empty.absurd({sc.stepc(SWord{buf, dd}, Lex.COther{}, ch) == sc.stepc(sc.fin(SWord{buf, dd}), Lex.COther{},
            ch) : Sc}, M1.true_false(h))
    case SIn{_dd}:
      {==}
    case SEsc{_dd}:
      {==}
    case SBad{}:
      {==}

# the scan after two texts, the first's end described
law tr:
  for +aa: String
  for +bb: String
  for +xx: Sc
  for +mid: Sc
  for +out: Sc
  for ha: {sc.fin(sc.run(aa, xx)) == mid : Sc}
  for hb: @yy: Sc -> {sc.fin(yy) == mid : Sc} -> {sc.fin(sc.run(bb, yy)) == out : Sc}
  {sc.fin(sc.run(aa ++ bb, xx)) == out : Sc}

def tr(aa, bb, xx, _mid, out, ha, hb):
  Equal.trans(Sc, sc.fin(sc.run(aa ++ bb, xx)), sc.fin(sc.run(bb, sc.run(aa, xx))), out,
    Equal.cong(Sc, Sc, zz => sc.fin(zz), sc.run(aa ++ bb, xx), sc.run(bb, sc.run(aa, xx)), sc_app(aa, bb, xx)),
    hb(sc.run(aa, xx), ha))

# one character that is no word character, the scan before it described
law p_ch:
  for +ch: Char
  for h_nw: {is_oth(Lex.classify(ch)) == False{} : Bool}
  for +aa: Sc
  for +yy: Sc
  for hy: {sc.fin(yy) == aa : Sc}
  {sc.fin(sc.run(SCon{ch, ""}, yy)) == sc.fin(sc.stepc(aa, Lex.classify(ch), ch)) : Sc}

def p_ch(ch, h_nw, aa, yy, hy):
  Equal.trans(Sc, sc.fin(sc.stepc(yy, Lex.classify(ch), ch)), sc.fin(sc.stepc(sc.fin(yy), Lex.classify(ch), ch)),
    sc.fin(sc.stepc(aa, Lex.classify(ch), ch)),
    Equal.cong(Sc, Sc, zz => sc.fin(zz), sc.stepc(yy, Lex.classify(ch), ch), sc.stepc(sc.fin(yy), Lex.classify(ch),
      ch), fin_stepc(yy, Lex.classify(ch), ch, h_nw)),
    Equal.cong(Sc, Sc, zz => sc.fin(sc.stepc(zz, Lex.classify(ch), ch)), sc.fin(yy), aa, hy))

# a whitespace character's class
law ws_cls:
  for +ch: Char
  for h: {D1.is_ws(ch) == True{} : Bool}
  {Lex.classify(ch) == Lex.CSpace{} : Lex.Class}

def ws_cls(ch, h):
  match ch:
    case Chr{+uu}:
      M4.ws_a(uu, U32.is_eq(uu, 32), {==}, h)

# whitespace leaves the scan outside strings where it is
law p_ws:
  for +ww: String
  for +h_w: {D1.all_ws(ww) == True{} : Bool}
  for +lt: Lt
  for +dd: Nat
  for +yy: Sc
  for +hy: {sc.fin(yy) == SOut{lt, dd} : Sc}
  {sc.fin(sc.run(ww, yy)) == SOut{lt, dd} : Sc}

def p_ws(ww, h_w, lt, dd, yy, hy):
  match ww:
    case SNil{}:
      hy
    case SCon{+hd, +tl}:
      +ecl = ws_cls(hd, M3.and_left(D1.is_ws(hd), D1.all_ws(tl), h_w))
      Equal.trans(Sc, sc.fin(sc.run(tl, sc.stepc(yy, Lex.classify(hd), hd))), sc.fin(sc.run(tl, SOut{lt, dd})),
        SOut{lt, dd},
        Equal.cong(Sc, Sc, zz => sc.fin(sc.run(tl, zz)), sc.stepc(yy, Lex.classify(hd), hd), SOut{lt, dd},
          Equal.trans(Sc, sc.stepc(yy, Lex.classify(hd), hd), sc.stepc(sc.fin(yy), Lex.classify(hd), hd), SOut{lt, dd},
            fin_stepc(yy, Lex.classify(hd), hd, Equal.cong(Lex.Class, Bool, zz => is_oth(zz), Lex.classify(hd),
              Lex.CSpace{}, ecl)),
            Equal.trans(Sc, sc.stepc(sc.fin(yy), Lex.classify(hd), hd), sc.stepc(SOut{lt, dd}, Lex.classify(hd), hd),
              SOut{lt, dd},
              Equal.cong(Sc, Sc, zz => sc.stepc(zz, Lex.classify(hd), hd), sc.fin(yy), SOut{lt, dd}, hy),
              Equal.cong(Lex.Class, Sc, zz => sc.out(lt, dd, zz, hd), Lex.classify(hd), Lex.CSpace{}, ecl)))),
        p_ws(tl, M3.and_right(D1.is_ws(hd), D1.all_ws(tl), h_w), lt, dd, SOut{lt, dd}, {==}))

# the scan outside strings
def is_out(st: Sc) -> Bool:
  match st:
    case SOut{_, _}:
      True{}
    case _:
      False{}

# the scan in a string
def is_in(st: Sc) -> Bool:
  match st:
    case SIn{_}:
      True{}
    case _:
      False{}

# what may come next, outside strings
def lt_of(st: Sc) -> Lt:
  match st:
    case SOut{lt, _}:
      lt
    case _:
      LSt{}

# a word's end described as not a value's: a word was not read
law fin_ex_w:
  for bv: Bool
  for +dd: Nat
  for +lt: Lt
  for +ee: Nat
  for hy: {Bool.pick(Sc, bv, SOut{LVal{}, dd}, SBad{}) == SOut{lt, ee} : Sc}
  for h_lt: {notval(lt) == True{} : Bool}
  Empty

def fin_ex_w(bv, dd, lt, ee, hy, h_lt):
  match bv:
    case True{}:
      M3.false_true(Equal.trans(Bool, False{}, notval(lt), True{}, Equal.cong(Sc, Bool, zz => notval(lt_of(zz)),
        SOut{LVal{}, dd}, SOut{lt, ee}, hy), h_lt))
    case False{}:
      M3.false_true(Equal.cong(Sc, Bool, zz => is_out(zz), SBad{}, SOut{lt, ee}, hy))

# a scan whose end is outside strings, where a value may come, is there
law fin_ex_o:
  for +yy: Sc
  for +lt: Lt
  for +dd: Nat
  for hy: {sc.fin(yy) == SOut{lt, dd} : Sc}
  for h_lt: {notval(lt) == True{} : Bool}
  {yy == SOut{lt, dd} : Sc}

def fin_ex_o(yy, lt, dd, hy, h_lt):
  match yy:
    case SOut{_l, _d}:
      hy
    case SWord{+buf, +ee}:
      Empty.absurd({SWord{buf, ee} == SOut{lt, dd} : Sc}, fin_ex_w(D1.lit_or_num(Lex.text(buf)), ee, lt, dd, hy,
        h_lt))
    case SIn{+ee}:
      Empty.absurd({SIn{ee} == SOut{lt, dd} : Sc}, M3.false_true(Equal.cong(Sc, Bool, zz => is_out(zz), SIn{ee},
        SOut{lt, dd}, hy)))
    case SEsc{+ee}:
      Empty.absurd({SEsc{ee} == SOut{lt, dd} : Sc}, M3.false_true(Equal.cong(Sc, Bool, zz => is_out(zz), SEsc{ee},
        SOut{lt, dd}, hy)))
    case SBad{}:
      Empty.absurd({SBad{} == SOut{lt, dd} : Sc}, M3.false_true(Equal.cong(Sc, Bool, zz => is_out(zz), SBad{},
        SOut{lt, dd}, hy)))

# a word's end is not in a string
law fin_ex_wi:
  for bv: Bool
  for +dd: Nat
  for +ee: Nat
  for hy: {Bool.pick(Sc, bv, SOut{LVal{}, dd}, SBad{}) == SIn{ee} : Sc}
  Empty

def fin_ex_wi(bv, dd, ee, hy):
  match bv:
    case True{}:
      M3.false_true(Equal.cong(Sc, Bool, zz => is_in(zz), SOut{LVal{}, dd}, SIn{ee}, hy))
    case False{}:
      M3.false_true(Equal.cong(Sc, Bool, zz => is_in(zz), SBad{}, SIn{ee}, hy))

# a scan whose end is in a string is there
law fin_ex_i:
  for +yy: Sc
  for +dd: Nat
  for hy: {sc.fin(yy) == SIn{dd} : Sc}
  {yy == SIn{dd} : Sc}

def fin_ex_i(yy, dd, hy):
  match yy:
    case SOut{+l, +ee}:
      Empty.absurd({SOut{l, ee} == SIn{dd} : Sc}, M3.false_true(Equal.cong(Sc, Bool, zz => is_in(zz), SOut{l, ee},
        SIn{dd}, hy)))
    case SWord{+buf, +ee}:
      Empty.absurd({SWord{buf, ee} == SIn{dd} : Sc}, fin_ex_wi(D1.lit_or_num(Lex.text(buf)), ee, dd, hy))
    case SIn{_ee}:
      hy
    case SEsc{+ee}:
      Empty.absurd({SEsc{ee} == SIn{dd} : Sc}, M3.false_true(Equal.cong(Sc, Bool, zz => is_in(zz), SEsc{ee},
        SIn{dd}, hy)))
    case SBad{}:
      Empty.absurd({SBad{} == SIn{dd} : Sc}, M3.false_true(Equal.cong(Sc, Bool, zz => is_in(zz), SBad{}, SIn{dd}, hy)))

# cells start after a value
law lv_eq:
  for +lt: Lt
  for h: {Bool.not(notval(lt)) == True{} : Bool}
  {lt == LVal{} : Lt}

def lv_eq(lt, h):
  match lt:
    case LSt{}:
      M3.no({LSt{} == LVal{} : Lt}, h)
    case LOp{}:
      M3.no({LOp{} == LVal{} : Lt}, h)
    case LVal{}:
      {==}

# an open bracket where a value may come
law open_ok:
  for +lt: Lt
  for +dd: Nat
  for h: {notval(lt) == True{} : Bool}
  {sc.open(lt, dd) == SOut{LOp{}, 1n+dd} : Sc}

def open_ok(lt, dd, h):
  match lt:
    case LSt{}:
      {==}
    case LOp{}:
      {==}
    case LVal{}:
      M3.no({sc.open(LVal{}, dd) == SOut{LOp{}, 1n+dd} : Sc}, h)

# a quotation mark where a value may come
law quote_ok:
  for +lt: Lt
  for +dd: Nat
  for h: {notval(lt) == True{} : Bool}
  {sc.quote(lt, dd) == SIn{dd} : Sc}

def quote_ok(lt, dd, h):
  match lt:
    case LSt{}:
      {==}
    case LOp{}:
      {==}
    case LVal{}:
      M3.no({sc.quote(LVal{}, dd) == SIn{dd} : Sc}, h)

# a word's first character where a value may come
law wstart_ok:
  for +lt: Lt
  for +dd: Nat
  for +ch: Char
  for h: {notval(lt) == True{} : Bool}
  {sc.wstart(lt, dd, ch) == SWord{[ch], dd} : Sc}

def wstart_ok(lt, dd, ch, h):
  match lt:
    case LSt{}:
      {==}
    case LOp{}:
      {==}
    case LVal{}:
      M3.no({sc.wstart(LVal{}, dd, ch) == SWord{[ch], dd} : Sc}, h)

# word characters in a word
law wrun:
  for +cs: String
  for h: M8.others(String.to_list(cs))
  for +buf: List<&2, Char>
  for +dd: Nat
  {sc.run(cs, SWord{buf, dd}) == SWord{List.reverse.go(&2, Char, String.to_list(cs), buf), dd} : Sc}

def wrun(cs, h, buf, dd):
  match cs:
    case SNil{}:
      {==}
    case SCon{+hd, +tl}:
      (h1, h2) = h
      Equal.trans(Sc, sc.run(tl, sc.word(buf, dd, Lex.classify(hd), hd)), sc.run(tl, SWord{hd <> buf, dd}),
        SWord{List.reverse.go(&2, Char, String.to_list(tl), hd <> buf), dd},
        Equal.cong(Lex.Class, Sc, zz => sc.run(tl, sc.word(buf, dd, zz, hd)), Lex.classify(hd), Lex.COther{}, h1),
        wrun(tl, h2, hd <> buf, dd))

# a word read from where a value may come
law wrun0:
  for +hd: Char
  for +tl: String
  for h: M8.others(hd <> String.to_list(tl))
  for +lt: Lt
  for +dd: Nat
  for +h_lt: {notval(lt) == True{} : Bool}
  {sc.run(SCon{hd, tl}, SOut{lt, dd}) == SWord{List.reverse.go(&2, Char, String.to_list(tl), [hd]), dd} : Sc}

def wrun0(hd, tl, h, lt, dd, h_lt):
  (h1, h2) = h
  Equal.trans(Sc, sc.run(tl, sc.out(lt, dd, Lex.classify(hd), hd)), sc.run(tl, sc.wstart(lt, dd, hd)),
    SWord{List.reverse.go(&2, Char, String.to_list(tl), [hd]), dd},
    Equal.cong(Lex.Class, Sc, zz => sc.run(tl, sc.out(lt, dd, zz, hd)), Lex.classify(hd), Lex.COther{}, h1),
    Equal.trans(Sc, sc.run(tl, sc.wstart(lt, dd, hd)), sc.run(tl, SWord{[hd], dd}),
      SWord{List.reverse.go(&2, Char, String.to_list(tl), [hd]), dd},
      Equal.cong(Sc, Sc, zz => sc.run(tl, zz), sc.wstart(lt, dd, hd), SWord{[hd], dd}, wstart_ok(lt, dd, hd, h_lt)),
      wrun(tl, h2, [hd], dd)))

# a literal name or a number is word characters
law lon_oth.at:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for +w: String
  for e1: {String.eq(w, "null") == b1 : Bool}
  for e2: {String.eq(w, "true") == b2 : Bool}
  for e3: {String.eq(w, "false") == b3 : Bool}
  for h: {Bool.or(b1, Bool.or(b2, Bool.or(b3, D1.number(String.to_list(w))))) == True{} : Bool}
  M8.others(String.to_list(w))

def lon_oth.at(b1, b2, b3, w, e1, e2, e3, h):
  match b1:
    case True{}:
      ek = Equal.sym(String, w, "null", M5.str_eq_sound(w, "null", e1))
      %ek : M8.others(String.to_list(_))
      ({==}, ({==}, ({==}, ({==}, Unit{}))))
    case False{}:
      match b2:
        case True{}:
          ek = Equal.sym(String, w, "true", M5.str_eq_sound(w, "true", e2))
          %ek : M8.others(String.to_list(_))
          ({==}, ({==}, ({==}, ({==}, Unit{}))))
        case False{}:
          match b3:
            case True{}:
              ek = Equal.sym(String, w, "false", M5.str_eq_sound(w, "false", e3))
              %ek : M8.others(String.to_list(_))
              ({==}, ({==}, ({==}, ({==}, ({==}, Unit{})))))
            case False{}:
              M5.oth_number(String.to_list(w), h)

law lon_oth:
  for +w: String
  for h: {D1.lit_or_num(w) == True{} : Bool}
  M8.others(String.to_list(w))

def lon_oth(w, h):
  lon_oth.at(String.eq(w, "null"), String.eq(w, "true"), String.eq(w, "false"), w, {==}, {==}, {==}, h)

# a word read where a value may come ends where a value ends
law g1_word:
  for +w: String
  for +h_ok: {D1.lit_or_num(w) == True{} : Bool}
  for +lt: Lt
  for +dd: Nat
  for +h_lt: {notval(lt) == True{} : Bool}
  for +yy: Sc
  for +hy: {sc.fin(yy) == SOut{lt, dd} : Sc}
  {sc.fin(sc.run(w, yy)) == SOut{LVal{}, dd} : Sc}

def g1_word(w, h_ok, lt, dd, h_lt, yy, hy):
  match w:
    case SNil{}:
      M3.no({sc.fin(sc.run("", yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
    case SCon{+hd, +tl}:
      +rw = List.reverse.go(&2, Char, String.to_list(tl), [hd])
      Equal.trans(Sc, sc.fin(sc.run(SCon{hd, tl}, yy)), sc.fin(sc.run(SCon{hd, tl}, SOut{lt, dd})), SOut{LVal{}, dd},
        Equal.cong(Sc, Sc, zz => sc.fin(sc.run(SCon{hd, tl}, zz)), yy, SOut{lt, dd}, fin_ex_o(yy, lt, dd, hy, h_lt)),
        Equal.trans(Sc, sc.fin(sc.run(SCon{hd, tl}, SOut{lt, dd})), sc.fin(SWord{rw, dd}), SOut{LVal{}, dd},
          Equal.cong(Sc, Sc, zz => sc.fin(zz), sc.run(SCon{hd, tl}, SOut{lt, dd}), SWord{rw, dd}, wrun0(hd, tl,
            lon_oth(SCon{hd, tl}, h_ok), lt, dd, h_lt)),
          Equal.trans(Sc, sc.fin(SWord{rw, dd}), Bool.pick(Sc, D1.lit_or_num(SCon{hd, tl}), SOut{LVal{}, dd},
            SBad{}), SOut{LVal{}, dd},
            Equal.cong(String, Sc, zz => Bool.pick(Sc, D1.lit_or_num(zz), SOut{LVal{}, dd}, SBad{}), Lex.text(rw),
              SCon{hd, tl}, M3.word_text(SCon{hd, tl})),
            Equal.cong(Bool, Sc, zz => Bool.pick(Sc, zz, SOut{LVal{}, dd}, SBad{}), D1.lit_or_num(SCon{hd, tl}),
              True{}, h_ok))))

# RFC 8259's hexadecimal digit test on a code point
def hexu(+cp: U32) -> Bool:
  Bool.or(Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, 57)), Bool.or(Bool.and(U32.is_ge(cp, 65), U32.is_le(cp, 70)),
    Bool.and(U32.is_ge(cp, 97), U32.is_le(cp, 102))))

# a character in a string that is no quotation mark or reverse solidus
law in_nq:
  for +ch: Char
  for cls: Lex.Class
  for +e: {Lex.classify(ch) == cls : Lex.Class}
  for hq: {D1.is_cp(ch, 34) == False{} : Bool}
  for hb: {D1.is_cp(ch, 92) == False{} : Bool}
  for +dd: Nat
  {sc.in(dd, cls) == SIn{dd} : Sc}

def in_nq(ch, cls, e, hq, hb, dd):
  match cls:
    case Lex.CPunct{_tk}:
      {==}
    case Lex.CQuote{}:
      Empty.absurd({SOut{LVal{}, dd} == SIn{dd} : Sc}, M3.false_true(Equal.trans(Bool, False{}, D1.is_cp(ch, 34),
        True{}, Equal.sym(Bool, D1.is_cp(ch, 34), False{}, hq), Equal.cong(U32, Bool, zz => U32.is_eq(zz, 34),
        Char.to_u32(ch), 34, M2.cls_quote(ch, e)))))
    case Lex.CBack{}:
      Empty.absurd({SEsc{dd} == SIn{dd} : Sc}, M3.false_true(Equal.trans(Bool, False{}, D1.is_cp(ch, 92),
        True{}, Equal.sym(Bool, D1.is_cp(ch, 92), False{}, hb), Equal.cong(U32, Bool, zz => U32.is_eq(zz, 92),
        Char.to_u32(ch), 92, M2.cls_back(ch, e)))))
    case Lex.CSpace{}:
      {==}
    case Lex.COther{}:
      {==}

law in_step:
  for +ch: Char
  for +rest: String
  for hq: {D1.is_cp(ch, 34) == False{} : Bool}
  for hb: {D1.is_cp(ch, 92) == False{} : Bool}
  for +dd: Nat
  {sc.run(SCon{ch, rest}, SIn{dd}) == sc.run(rest, SIn{dd}) : Sc}

def in_step(ch, rest, hq, hb, dd):
  Equal.cong(Sc, Sc, zz => sc.run(rest, zz), sc.in(dd, Lex.classify(ch)), SIn{dd}, in_nq(ch, Lex.classify(ch), {==},
    hq, hb, dd))

# a hexadecimal digit is not the code point cp
law hex_ne.at:
  for bv: Bool
  for +ch: Char
  for +cp: U32
  for e: {D1.is_cp(ch, cp) == bv : Bool}
  for h: {D2.hexd(ch) == True{} : Bool}
  for n: {hexu(cp) == False{} : Bool}
  {D1.is_cp(ch, cp) == False{} : Bool}

def hex_ne.at(bv, ch, cp, e, h, n):
  match bv:
    case False{}:
      e
    case True{}:
      Empty.absurd({D1.is_cp(ch, cp) == False{} : Bool}, M1.true_false(Equal.trans(Bool, True{}, hexu(Char.to_u32(ch)),
        False{}, Equal.sym(Bool, D2.hexd(ch), True{}, h), Equal.trans(Bool, hexu(Char.to_u32(ch)), hexu(cp),
        False{}, Equal.cong(U32, Bool, zz => hexu(zz), Char.to_u32(ch), cp, M7.ueq(Char.to_u32(ch), cp, e)), n))))

law hex_ne:
  for +ch: Char
  for +cp: U32
  for h: {D2.hexd(ch) == True{} : Bool}
  for n: {hexu(cp) == False{} : Bool}
  {D1.is_cp(ch, cp) == False{} : Bool}

def hex_ne(ch, cp, h, n):
  hex_ne.at(D1.is_cp(ch, cp), ch, cp, {==}, h, n)

law hex_step:
  for +ch: Char
  for +rest: String
  for +h: {D2.hexd(ch) == True{} : Bool}
  for +dd: Nat
  {sc.run(SCon{ch, rest}, SIn{dd}) == sc.run(rest, SIn{dd}) : Sc}

def hex_step(ch, rest, h, dd):
  in_step(ch, rest, hex_ne(ch, 34, h, {==}), hex_ne(ch, 92, h, {==}), dd)

# a piece of a string, read in a string, leaves the scan in it
law pc_in:
  for +pc: D2.Piece
  for +h: {D2.piece.ok(pc) == True{} : Bool}
  for +dd: Nat
  {sc.run(D2.piece.text(pc), SIn{dd}) == SIn{dd} : Sc}

def pc_in(pc, h, dd):
  match pc:
    case D2.PRaw{+ch}:
      +nt = M6.not_true(Bool.or(D1.is_cp(ch, 34), Bool.or(D1.is_cp(ch, 92), U32.is_lt(Char.to_u32(ch), 32))), h)
      in_step(ch, "", M6.or_false_l(D1.is_cp(ch, 34), Bool.or(D1.is_cp(ch, 92), U32.is_lt(Char.to_u32(ch), 32)), nt),
        M6.or_false_l(D1.is_cp(ch, 92), U32.is_lt(Char.to_u32(ch), 32), M6.or_false_r(D1.is_cp(ch, 34),
        Bool.or(D1.is_cp(ch, 92), U32.is_lt(Char.to_u32(ch), 32)), nt)), dd)
    case D2.PEsc{_ch}:
      {==}
    case D2.PU{+a1, +a2, +a3, +a4}:
      Equal.trans(Sc, sc.run(SCon{a1, SCon{a2, SCon{a3, SCon{a4, ""}}}}, SIn{dd}), sc.run(SCon{a2, SCon{a3, SCon{a4,
        ""}}}, SIn{dd}), sc.run("", SIn{dd}), hex_step(a1, SCon{a2, SCon{a3, SCon{a4, ""}}}, M3.and_left(D2.hexd(a1),
        Bool.and(D2.hexd(a2), Bool.and(D2.hexd(a3), D2.hexd(a4))), M3.and_left(Bool.and(D2.hexd(a1),
        Bool.and(D2.hexd(a2), Bool.and(D2.hexd(a3), D2.hexd(a4)))), D2.non_sur(D2.hex4(a1, a2, a3, a4)), h)),
        dd), Equal.trans(Sc, sc.run(SCon{a2, SCon{a3, SCon{a4, ""}}}, SIn{dd}), sc.run(SCon{a3, SCon{a4, ""}},
        SIn{dd}), sc.run("", SIn{dd}), hex_step(a2, SCon{a3, SCon{a4, ""}}, M3.and_left(D2.hexd(a2),
        Bool.and(D2.hexd(a3), D2.hexd(a4)), M3.and_right(D2.hexd(a1), Bool.and(D2.hexd(a2),
        Bool.and(D2.hexd(a3), D2.hexd(a4))), M3.and_left(Bool.and(D2.hexd(a1), Bool.and(D2.hexd(a2),
        Bool.and(D2.hexd(a3), D2.hexd(a4)))), D2.non_sur(D2.hex4(a1, a2, a3, a4)), h))), dd), Equal.trans(Sc,
        sc.run(SCon{a3, SCon{a4, ""}}, SIn{dd}), sc.run(SCon{a4, ""}, SIn{dd}), sc.run("", SIn{dd}), hex_step(a3,
        SCon{a4, ""}, M3.and_left(D2.hexd(a3), D2.hexd(a4), M3.and_right(D2.hexd(a2), Bool.and(D2.hexd(a3),
        D2.hexd(a4)), M3.and_right(D2.hexd(a1), Bool.and(D2.hexd(a2), Bool.and(D2.hexd(a3), D2.hexd(a4))),
        M3.and_left(Bool.and(D2.hexd(a1), Bool.and(D2.hexd(a2), Bool.and(D2.hexd(a3), D2.hexd(a4)))),
        D2.non_sur(D2.hex4(a1, a2, a3, a4)), h)))), dd), hex_step(a4, "", M3.and_right(D2.hexd(a3), D2.hexd(a4),
        M3.and_right(D2.hexd(a2), Bool.and(D2.hexd(a3), D2.hexd(a4)), M3.and_right(D2.hexd(a1),
        Bool.and(D2.hexd(a2), Bool.and(D2.hexd(a3), D2.hexd(a4))), M3.and_left(Bool.and(D2.hexd(a1),
        Bool.and(D2.hexd(a2), Bool.and(D2.hexd(a3), D2.hexd(a4)))), D2.non_sur(D2.hex4(a1, a2, a3, a4)),
        h)))), dd))))
    case D2.PPair{+a1, +a2, +a3, +a4, +a5, +a6, +a7, +a8}:
      Equal.trans(Sc, sc.run(SCon{a1, SCon{a2, SCon{a3, SCon{a4, SCon{'\\', SCon{'u', SCon{a5, SCon{a6, SCon{a7,
        SCon{a8, ""}}}}}}}}}}, SIn{dd}), sc.run(SCon{a2, SCon{a3, SCon{a4, SCon{'\\', SCon{'u', SCon{a5, SCon{a6,
        SCon{a7, SCon{a8, ""}}}}}}}}}, SIn{dd}), sc.run("", SIn{dd}), hex_step(a1, SCon{a2, SCon{a3, SCon{a4,
        SCon{'\\', SCon{'u', SCon{a5, SCon{a6, SCon{a7, SCon{a8, ""}}}}}}}}}, M3.and_left(D2.hexd(a1),
        Bool.and(D2.hexd(a2), Bool.and(D2.hexd(a3), D2.hexd(a4))), M3.and_left(Bool.and(D2.hexd(a1),
        Bool.and(D2.hexd(a2), Bool.and(D2.hexd(a3), D2.hexd(a4)))), Bool.and(Bool.and(D2.hexd(a5),
        Bool.and(D2.hexd(a6), Bool.and(D2.hexd(a7), D2.hexd(a8)))), Bool.and(D2.in_hi(D2.hex4(a1, a2, a3,
        a4)), D2.lo_sur(D2.hex4(a5, a6, a7, a8)))), h)), dd), Equal.trans(Sc, sc.run(SCon{a2, SCon{a3, SCon{a4,
        SCon{'\\', SCon{'u', SCon{a5, SCon{a6, SCon{a7, SCon{a8, ""}}}}}}}}}, SIn{dd}), sc.run(SCon{a3, SCon{a4,
        SCon{'\\', SCon{'u', SCon{a5, SCon{a6, SCon{a7, SCon{a8, ""}}}}}}}}, SIn{dd}), sc.run("", SIn{dd}),
        hex_step(a2, SCon{a3, SCon{a4, SCon{'\\', SCon{'u', SCon{a5, SCon{a6, SCon{a7, SCon{a8, ""}}}}}}}},
        M3.and_left(D2.hexd(a2), Bool.and(D2.hexd(a3), D2.hexd(a4)), M3.and_right(D2.hexd(a1),
        Bool.and(D2.hexd(a2), Bool.and(D2.hexd(a3), D2.hexd(a4))), M3.and_left(Bool.and(D2.hexd(a1),
        Bool.and(D2.hexd(a2), Bool.and(D2.hexd(a3), D2.hexd(a4)))), Bool.and(Bool.and(D2.hexd(a5),
        Bool.and(D2.hexd(a6), Bool.and(D2.hexd(a7), D2.hexd(a8)))), Bool.and(D2.in_hi(D2.hex4(a1, a2, a3,
        a4)), D2.lo_sur(D2.hex4(a5, a6, a7, a8)))), h))), dd), Equal.trans(Sc, sc.run(SCon{a3, SCon{a4, SCon{'\\',
        SCon{'u', SCon{a5, SCon{a6, SCon{a7, SCon{a8, ""}}}}}}}}, SIn{dd}), sc.run(SCon{a4, SCon{'\\', SCon{'u',
        SCon{a5, SCon{a6, SCon{a7, SCon{a8, ""}}}}}}}, SIn{dd}), sc.run("", SIn{dd}), hex_step(a3, SCon{a4, SCon{'\\',
        SCon{'u', SCon{a5, SCon{a6, SCon{a7, SCon{a8, ""}}}}}}}, M3.and_left(D2.hexd(a3), D2.hexd(a4),
        M3.and_right(D2.hexd(a2), Bool.and(D2.hexd(a3), D2.hexd(a4)), M3.and_right(D2.hexd(a1),
        Bool.and(D2.hexd(a2), Bool.and(D2.hexd(a3), D2.hexd(a4))), M3.and_left(Bool.and(D2.hexd(a1),
        Bool.and(D2.hexd(a2), Bool.and(D2.hexd(a3), D2.hexd(a4)))), Bool.and(Bool.and(D2.hexd(a5),
        Bool.and(D2.hexd(a6), Bool.and(D2.hexd(a7), D2.hexd(a8)))), Bool.and(D2.in_hi(D2.hex4(a1, a2, a3,
        a4)), D2.lo_sur(D2.hex4(a5, a6, a7, a8)))), h)))), dd), Equal.trans(Sc, sc.run(SCon{a4, SCon{'\\',
        SCon{'u', SCon{a5, SCon{a6, SCon{a7, SCon{a8, ""}}}}}}}, SIn{dd}), sc.run(SCon{a5, SCon{a6, SCon{a7, SCon{a8,
        ""}}}}, SIn{dd}), sc.run("", SIn{dd}), hex_step(a4, SCon{'\\', SCon{'u', SCon{a5, SCon{a6, SCon{a7, SCon{a8,
        ""}}}}}}, M3.and_right(D2.hexd(a3), D2.hexd(a4), M3.and_right(D2.hexd(a2), Bool.and(D2.hexd(a3),
        D2.hexd(a4)), M3.and_right(D2.hexd(a1), Bool.and(D2.hexd(a2), Bool.and(D2.hexd(a3), D2.hexd(a4))),
        M3.and_left(Bool.and(D2.hexd(a1), Bool.and(D2.hexd(a2), Bool.and(D2.hexd(a3), D2.hexd(a4)))),
        Bool.and(Bool.and(D2.hexd(a5), Bool.and(D2.hexd(a6), Bool.and(D2.hexd(a7), D2.hexd(a8)))),
        Bool.and(D2.in_hi(D2.hex4(a1, a2, a3, a4)), D2.lo_sur(D2.hex4(a5, a6, a7, a8)))), h)))), dd),
        Equal.trans(Sc, sc.run(SCon{a5, SCon{a6, SCon{a7, SCon{a8, ""}}}}, SIn{dd}), sc.run(SCon{a6, SCon{a7, SCon{a8,
        ""}}}, SIn{dd}), sc.run("", SIn{dd}), hex_step(a5, SCon{a6, SCon{a7, SCon{a8, ""}}}, M3.and_left(D2.hexd(a5),
        Bool.and(D2.hexd(a6), Bool.and(D2.hexd(a7), D2.hexd(a8))), M3.and_left(Bool.and(D2.hexd(a5),
        Bool.and(D2.hexd(a6), Bool.and(D2.hexd(a7), D2.hexd(a8)))), Bool.and(D2.in_hi(D2.hex4(a1, a2, a3,
        a4)), D2.lo_sur(D2.hex4(a5, a6, a7, a8))), M3.and_right(Bool.and(D2.hexd(a1), Bool.and(D2.hexd(a2),
        Bool.and(D2.hexd(a3), D2.hexd(a4)))), Bool.and(Bool.and(D2.hexd(a5), Bool.and(D2.hexd(a6),
        Bool.and(D2.hexd(a7), D2.hexd(a8)))), Bool.and(D2.in_hi(D2.hex4(a1, a2, a3, a4)),
        D2.lo_sur(D2.hex4(a5, a6, a7, a8)))), h))), dd), Equal.trans(Sc, sc.run(SCon{a6, SCon{a7, SCon{a8, ""}}},
        SIn{dd}), sc.run(SCon{a7, SCon{a8, ""}}, SIn{dd}), sc.run("", SIn{dd}), hex_step(a6, SCon{a7, SCon{a8, ""}},
        M3.and_left(D2.hexd(a6), Bool.and(D2.hexd(a7), D2.hexd(a8)), M3.and_right(D2.hexd(a5),
        Bool.and(D2.hexd(a6), Bool.and(D2.hexd(a7), D2.hexd(a8))), M3.and_left(Bool.and(D2.hexd(a5),
        Bool.and(D2.hexd(a6), Bool.and(D2.hexd(a7), D2.hexd(a8)))), Bool.and(D2.in_hi(D2.hex4(a1, a2, a3,
        a4)), D2.lo_sur(D2.hex4(a5, a6, a7, a8))), M3.and_right(Bool.and(D2.hexd(a1), Bool.and(D2.hexd(a2),
        Bool.and(D2.hexd(a3), D2.hexd(a4)))), Bool.and(Bool.and(D2.hexd(a5), Bool.and(D2.hexd(a6),
        Bool.and(D2.hexd(a7), D2.hexd(a8)))), Bool.and(D2.in_hi(D2.hex4(a1, a2, a3, a4)),
        D2.lo_sur(D2.hex4(a5, a6, a7, a8)))), h)))), dd), Equal.trans(Sc, sc.run(SCon{a7, SCon{a8, ""}}, SIn{dd}),
        sc.run(SCon{a8, ""}, SIn{dd}), sc.run("", SIn{dd}), hex_step(a7, SCon{a8, ""}, M3.and_left(D2.hexd(a7),
        D2.hexd(a8), M3.and_right(D2.hexd(a6), Bool.and(D2.hexd(a7), D2.hexd(a8)), M3.and_right(D2.hexd(a5),
        Bool.and(D2.hexd(a6), Bool.and(D2.hexd(a7), D2.hexd(a8))), M3.and_left(Bool.and(D2.hexd(a5),
        Bool.and(D2.hexd(a6), Bool.and(D2.hexd(a7), D2.hexd(a8)))), Bool.and(D2.in_hi(D2.hex4(a1, a2, a3,
        a4)), D2.lo_sur(D2.hex4(a5, a6, a7, a8))), M3.and_right(Bool.and(D2.hexd(a1), Bool.and(D2.hexd(a2),
        Bool.and(D2.hexd(a3), D2.hexd(a4)))), Bool.and(Bool.and(D2.hexd(a5), Bool.and(D2.hexd(a6),
        Bool.and(D2.hexd(a7), D2.hexd(a8)))), Bool.and(D2.in_hi(D2.hex4(a1, a2, a3, a4)),
        D2.lo_sur(D2.hex4(a5, a6, a7, a8)))), h))))), dd), hex_step(a8, "", M3.and_right(D2.hexd(a7), D2.hexd(a8),
        M3.and_right(D2.hexd(a6), Bool.and(D2.hexd(a7), D2.hexd(a8)), M3.and_right(D2.hexd(a5),
        Bool.and(D2.hexd(a6), Bool.and(D2.hexd(a7), D2.hexd(a8))), M3.and_left(Bool.and(D2.hexd(a5),
        Bool.and(D2.hexd(a6), Bool.and(D2.hexd(a7), D2.hexd(a8)))), Bool.and(D2.in_hi(D2.hex4(a1, a2, a3,
        a4)), D2.lo_sur(D2.hex4(a5, a6, a7, a8))), M3.and_right(Bool.and(D2.hexd(a1), Bool.and(D2.hexd(a2),
        Bool.and(D2.hexd(a3), D2.hexd(a4)))), Bool.and(Bool.and(D2.hexd(a5), Bool.and(D2.hexd(a6),
        Bool.and(D2.hexd(a7), D2.hexd(a8)))), Bool.and(D2.in_hi(D2.hex4(a1, a2, a3, a4)),
        D2.lo_sur(D2.hex4(a5, a6, a7, a8)))), h))))), dd))))))))

# a string's pieces, read in a string, leave the scan in it
law sp_in:
  for +ps: List<&2, D2.Piece>
  for +h: {D2.spell_ok(ps) == True{} : Bool}
  for +dd: Nat
  {sc.run(D2.spell(ps), SIn{dd}) == SIn{dd} : Sc}

def sp_in(ps, h, dd):
  match ps:
    case Nil{}:
      {==}
    case +pc <> +tl:
      Equal.trans(Sc, sc.run(D2.piece.text(pc) ++ D2.spell(tl), SIn{dd}), sc.run(D2.spell(tl),
        sc.run(D2.piece.text(pc), SIn{dd})), SIn{dd}, sc_app(D2.piece.text(pc), D2.spell(tl), SIn{dd}),
        Equal.trans(Sc, sc.run(D2.spell(tl), sc.run(D2.piece.text(pc), SIn{dd})), sc.run(D2.spell(tl), SIn{dd}),
          SIn{dd}, Equal.cong(Sc, Sc, zz => sc.run(D2.spell(tl), zz), sc.run(D2.piece.text(pc), SIn{dd}), SIn{dd},
          pc_in(pc, M3.and_left(D2.piece.ok(pc), D2.spell_ok(tl), h), dd)),
          sp_in(tl, M3.and_right(D2.piece.ok(pc), D2.spell_ok(tl), h), dd)))

# a string's pieces, the scan before them described
law p_sp:
  for +ps: List<&2, D2.Piece>
  for +h: {D2.spell_ok(ps) == True{} : Bool}
  for +dd: Nat
  for +yy: Sc
  for +hy: {sc.fin(yy) == SIn{dd} : Sc}
  {sc.fin(sc.run(D2.spell(ps), yy)) == SIn{dd} : Sc}

def p_sp(ps, h, dd, yy, hy):
  Equal.cong(Sc, Sc, zz => sc.fin(zz), sc.run(D2.spell(ps), yy), SIn{dd}, Equal.trans(Sc, sc.run(D2.spell(ps), yy),
    sc.run(D2.spell(ps), SIn{dd}), SIn{dd}, Equal.cong(Sc, Sc, zz => sc.run(D2.spell(ps), zz), yy, SIn{dd},
    fin_ex_i(yy, dd, hy)), sp_in(ps, h, dd)))

# a derivation's text, read from where it may start, ends where a value
# ends: at the depth it started, a value just read
law g1:
  for +gg: D2.Gv
  for +kk: D2.GK
  for +h_ok: {D2.g.ok(gg, kk) == True{} : Bool}
  for +lt: Lt
  for +dd: Nat
  for +h_lt: {okl(kk, lt) == True{} : Bool}
  for +yy: Sc
  for +hy: {sc.fin(yy) == SOut{lt, dd} : Sc}
  {sc.fin(sc.run(D2.g.text(gg), yy)) == SOut{LVal{}, dd} : Sc}

def g1(gg, kk, h_ok, lt, dd, h_lt, yy, hy):
  match gg:
    case D2.GWord{+a1}:
      match kk:
        case D2.GKVal{}:
          g1_word(a1, h_ok, lt, dd, h_lt, yy, hy)
        case D2.GKArr{}:
          M3.no({sc.fin(sc.run(D2.g.text(D2.GWord{a1}), yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
        case D2.GKObj{}:
          M3.no({sc.fin(sc.run(D2.g.text(D2.GWord{a1}), yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
    case D2.GStr{+a1}:
      match kk:
        case D2.GKVal{}:
          tr("\"", D2.spell(a1) ++ "\"", yy, SIn{dd}, SOut{LVal{}, dd}, Equal.trans(Sc, sc.fin(sc.run("\"", yy)),
            sc.fin(sc.quote(lt, dd)), SIn{dd}, p_ch('"', {==}, SOut{lt, dd}, yy, hy), Equal.cong(Sc, Sc,
            zz => sc.fin(zz), sc.quote(lt, dd), SIn{dd}, quote_ok(lt, dd, h_lt))), +y0 => e0 => tr(D2.spell(a1),
            "\"", y0, SIn{dd}, SOut{LVal{}, dd}, p_sp(a1, h_ok, dd, y0, e0), +y1 => e1 => p_ch('"', {==}, SIn{dd}, y1,
            e1)))
        case D2.GKArr{}:
          M3.no({sc.fin(sc.run(D2.g.text(D2.GStr{a1}), yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
        case D2.GKObj{}:
          M3.no({sc.fin(sc.run(D2.g.text(D2.GStr{a1}), yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
    case D2.GArr0{+a1}:
      match kk:
        case D2.GKVal{}:
          tr("[", a1 ++ "]", yy, SOut{LOp{}, 1n+dd}, SOut{LVal{}, dd}, Equal.trans(Sc, sc.fin(sc.run(SCon{'[', ""},
            yy)), sc.fin(sc.open(lt, dd)), SOut{LOp{}, 1n+dd}, p_ch('[', {==}, SOut{lt, dd}, yy, hy), Equal.cong(Sc,
            Sc, zz => sc.fin(zz), sc.open(lt, dd), SOut{LOp{}, 1n+dd}, open_ok(lt, dd, h_lt))), +y0 => e0 => tr(a1,
            "]", y0, SOut{LOp{}, 1n+dd}, SOut{LVal{}, dd}, p_ws(a1, h_ok, LOp{}, 1n+dd, y0, e0), +y1 => e1 => p_ch(']',
            {==}, SOut{LOp{}, 1n+dd}, y1, e1)))
        case D2.GKArr{}:
          M3.no({sc.fin(sc.run(D2.g.text(D2.GArr0{a1}), yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
        case D2.GKObj{}:
          M3.no({sc.fin(sc.run(D2.g.text(D2.GArr0{a1}), yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
    case D2.GArr{+a1, +a2, +a3, +a4}:
      match kk:
        case D2.GKVal{}:
          tr("[", a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4) ++ "]", yy, SOut{LOp{}, 1n+dd}, SOut{LVal{}, dd},
            Equal.trans(Sc, sc.fin(sc.run(SCon{'[', ""}, yy)), sc.fin(sc.open(lt, dd)), SOut{LOp{}, 1n+dd}, p_ch('[',
            {==}, SOut{lt, dd}, yy, hy), Equal.cong(Sc, Sc, zz => sc.fin(zz), sc.open(lt, dd), SOut{LOp{}, 1n+dd},
            open_ok(lt, dd, h_lt))), +y0 => e0 => tr(a1, D2.g.text(a2) ++ a3 ++ D2.g.text(a4) ++ "]", y0,
            SOut{LOp{}, 1n+dd}, SOut{LVal{}, dd}, p_ws(a1, M3.and_left(D1.all_ws(a1), Bool.and(D2.g.ok(a2,
            D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}))), h_ok), LOp{}, 1n+dd, y0, e0),
            +y1 => e1 => tr(D2.g.text(a2), a3 ++ D2.g.text(a4) ++ "]", y1, SOut{LVal{}, 1n+dd}, SOut{LVal{}, dd},
            g1(a2, D2.GKVal{}, M3.and_left(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4,
            D2.GKArr{})), M3.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3),
            D2.g.ok(a4, D2.GKArr{}))), h_ok)), LOp{}, 1n+dd, {==}, y1, e1), +y2 => e2 => tr(a3,
            D2.g.text(a4) ++ "]", y2, SOut{LVal{}, 1n+dd}, SOut{LVal{}, dd}, p_ws(a3, M3.and_left(D1.all_ws(a3),
            D2.g.ok(a4, D2.GKArr{}), M3.and_right(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4,
            D2.GKArr{})), M3.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3),
            D2.g.ok(a4, D2.GKArr{}))), h_ok))), LVal{}, 1n+dd, y2, e2), +y3 => e3 => tr(D2.g.text(a4), "]", y3,
            SOut{LVal{}, 1n+dd}, SOut{LVal{}, dd}, g1(a4, D2.GKArr{}, M3.and_right(D1.all_ws(a3), D2.g.ok(a4,
            D2.GKArr{}), M3.and_right(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4,
            D2.GKArr{})), M3.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3),
            D2.g.ok(a4, D2.GKArr{}))), h_ok))), LVal{}, 1n+dd, {==}, y3, e3), +y4 => e4 => p_ch(']', {==},
            SOut{LVal{}, 1n+dd}, y4, e4))))))
        case D2.GKArr{}:
          M3.no({sc.fin(sc.run(D2.g.text(D2.GArr{a1, a2, a3, a4}), yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
        case D2.GKObj{}:
          M3.no({sc.fin(sc.run(D2.g.text(D2.GArr{a1, a2, a3, a4}), yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
    case D2.GObj0{+a1}:
      match kk:
        case D2.GKVal{}:
          tr("{", a1 ++ "}", yy, SOut{LOp{}, 1n+dd}, SOut{LVal{}, dd}, Equal.trans(Sc, sc.fin(sc.run(SCon{'{', ""},
            yy)), sc.fin(sc.open(lt, dd)), SOut{LOp{}, 1n+dd}, p_ch('{', {==}, SOut{lt, dd}, yy, hy), Equal.cong(Sc,
            Sc, zz => sc.fin(zz), sc.open(lt, dd), SOut{LOp{}, 1n+dd}, open_ok(lt, dd, h_lt))), +y0 => e0 => tr(a1,
            "}", y0, SOut{LOp{}, 1n+dd}, SOut{LVal{}, dd}, p_ws(a1, h_ok, LOp{}, 1n+dd, y0, e0), +y1 => e1 => p_ch('}',
            {==}, SOut{LOp{}, 1n+dd}, y1, e1)))
        case D2.GKArr{}:
          M3.no({sc.fin(sc.run(D2.g.text(D2.GObj0{a1}), yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
        case D2.GKObj{}:
          M3.no({sc.fin(sc.run(D2.g.text(D2.GObj0{a1}), yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
    case D2.GObj{+a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      match kk:
        case D2.GKVal{}:
          tr("{",
            a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++ D2.g.text(a7) ++ "}",
            yy, SOut{LOp{}, 1n+dd}, SOut{LVal{}, dd}, Equal.trans(Sc, sc.fin(sc.run(SCon{'{', ""}, yy)),
            sc.fin(sc.open(lt, dd)), SOut{LOp{}, 1n+dd}, p_ch('{', {==}, SOut{lt, dd}, yy, hy), Equal.cong(Sc, Sc,
            zz => sc.fin(zz), sc.open(lt, dd), SOut{LOp{}, 1n+dd}, open_ok(lt, dd, h_lt))), +y0 => e0 => tr(a1,
            "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++ D2.g.text(a7) ++ "}", y0,
            SOut{LOp{}, 1n+dd}, SOut{LVal{}, dd}, p_ws(a1, M3.and_left(D1.all_ws(a1), Bool.and(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h_ok), LOp{}, 1n+dd, y0, e0),
            +y1 => e1 => tr("\"",
            D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++ D2.g.text(a7) ++ "}", y1,
            SIn{1n+dd}, SOut{LVal{}, dd}, p_ch('"', {==}, SOut{LOp{}, 1n+dd}, y1, e1), +y2 => e2 => tr(D2.spell(a2),
            "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++ D2.g.text(a7) ++ "}", y2, SIn{1n+dd}, SOut{LVal{},
            dd}, p_sp(a2, M3.and_left(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))),
            M3.and_right(D1.all_ws(a1), Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h_ok)),
            1n+dd, y2, e2), +y3 => e3 => tr("\"", a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++ D2.g.text(a7) ++ "}",
            y3, SOut{LVal{}, 1n+dd}, SOut{LVal{}, dd}, p_ch('"', {==}, SIn{1n+dd}, y3, e3), +y4 => e4 => tr(a3,
            ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++ D2.g.text(a7) ++ "}", y4, SOut{LVal{}, 1n+dd}, SOut{LVal{}, dd},
            p_ws(a3, M3.and_left(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M3.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M3.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h_ok))), LVal{}, 1n+dd, y4, e4),
            +y5 => e5 => tr(":", a4 ++ D2.g.text(a5) ++ a6 ++ D2.g.text(a7) ++ "}", y5, SOut{LSt{}, 1n+dd},
            SOut{LVal{}, dd}, p_ch(':', {==}, SOut{LVal{}, 1n+dd}, y5, e5), +y6 => e6 => tr(a4,
            D2.g.text(a5) ++ a6 ++ D2.g.text(a7) ++ "}", y6, SOut{LSt{}, 1n+dd}, SOut{LVal{}, dd}, p_ws(a4,
            M3.and_left(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{}))), M3.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M3.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M3.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h_ok)))), LSt{}, 1n+dd, y6, e6),
            +y7 => e7 => tr(D2.g.text(a5), a6 ++ D2.g.text(a7) ++ "}", y7, SOut{LVal{}, 1n+dd}, SOut{LVal{}, dd},
            g1(a5, D2.GKVal{}, M3.and_left(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{})), M3.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6),
            D2.g.ok(a7, D2.GKObj{}))), M3.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M3.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M3.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h_ok))))), LSt{}, 1n+dd, {==},
            y7, e7), +y8 => e8 => tr(a6, D2.g.text(a7) ++ "}", y8, SOut{LVal{}, 1n+dd}, SOut{LVal{}, dd}, p_ws(a6,
            M3.and_left(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}), M3.and_right(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})), M3.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))), M3.and_right(D1.all_ws(a3),
            Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{})))), M3.and_right(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))),
            M3.and_right(D1.all_ws(a1), Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))),
            h_ok)))))), LVal{}, 1n+dd, y8, e8), +y9 => e9 => tr(D2.g.text(a7), "}", y9, SOut{LVal{}, 1n+dd},
            SOut{LVal{}, dd}, g1(a7, D2.GKObj{}, M3.and_right(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}),
            M3.and_right(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})),
            M3.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{}))), M3.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M3.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M3.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h_ok)))))), LVal{}, 1n+dd, {==},
            y9, e9), +y10 => e10 => p_ch('}', {==}, SOut{LVal{}, 1n+dd}, y10, e10))))))))))))
        case D2.GKArr{}:
          M3.no({sc.fin(sc.run(D2.g.text(D2.GObj{a1, a2, a3, a4, a5, a6, a7}), yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
        case D2.GKObj{}:
          M3.no({sc.fin(sc.run(D2.g.text(D2.GObj{a1, a2, a3, a4, a5, a6, a7}), yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
    case D2.GEnd{}:
      match kk:
        case D2.GKVal{}:
          M3.no({sc.fin(sc.run(D2.g.text(D2.GEnd{}), yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
        case D2.GKArr{}:
          hv = Equal.trans(Sc, sc.fin(yy), SOut{lt, dd}, SOut{LVal{}, dd}, hy, Equal.cong(Lt, Sc, zz => SOut{zz, dd},
            lt, LVal{}, lv_eq(lt, h_lt)))
          hv
        case D2.GKObj{}:
          hv = Equal.trans(Sc, sc.fin(yy), SOut{lt, dd}, SOut{LVal{}, dd}, hy, Equal.cong(Lt, Sc, zz => SOut{zz, dd},
            lt, LVal{}, lv_eq(lt, h_lt)))
          hv
    case D2.GNext{+a1, +a2, +a3, +a4}:
      match kk:
        case D2.GKVal{}:
          M3.no({sc.fin(sc.run(D2.g.text(D2.GNext{a1, a2, a3, a4}), yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
        case D2.GKArr{}:
          hv = Equal.trans(Sc, sc.fin(yy), SOut{lt, dd}, SOut{LVal{}, dd}, hy, Equal.cong(Lt, Sc, zz => SOut{zz, dd},
            lt, LVal{}, lv_eq(lt, h_lt)))
          tr(",", a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4), yy, SOut{LSt{}, dd}, SOut{LVal{}, dd}, p_ch(',',
            {==}, SOut{LVal{}, dd}, yy, hv), +y0 => e0 => tr(a1, D2.g.text(a2) ++ a3 ++ D2.g.text(a4), y0,
            SOut{LSt{}, dd}, SOut{LVal{}, dd}, p_ws(a1, M3.and_left(D1.all_ws(a1), Bool.and(D2.g.ok(a2, D2.GKVal{}),
            Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}))), h_ok), LSt{}, dd, y0, e0),
            +y1 => e1 => tr(D2.g.text(a2), a3 ++ D2.g.text(a4), y1, SOut{LVal{}, dd}, SOut{LVal{}, dd}, g1(a2,
            D2.GKVal{}, M3.and_left(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{})),
            M3.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4,
            D2.GKArr{}))), h_ok)), LSt{}, dd, {==}, y1, e1), +y2 => e2 => tr(a3, D2.g.text(a4), y2, SOut{LVal{},
            dd}, SOut{LVal{}, dd}, p_ws(a3, M3.and_left(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}),
            M3.and_right(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{})),
            M3.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4,
            D2.GKArr{}))), h_ok))), LVal{}, dd, y2, e2), +y3 => e3 => g1(a4, D2.GKArr{}, M3.and_right(D1.all_ws(a3),
            D2.g.ok(a4, D2.GKArr{}), M3.and_right(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4,
            D2.GKArr{})), M3.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3),
            D2.g.ok(a4, D2.GKArr{}))), h_ok))), LVal{}, dd, {==}, y3, e3)))))
        case D2.GKObj{}:
          M3.no({sc.fin(sc.run(D2.g.text(D2.GNext{a1, a2, a3, a4}), yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
    case D2.GNextM{+a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      match kk:
        case D2.GKVal{}:
          M3.no({sc.fin(sc.run(D2.g.text(D2.GNextM{a1, a2, a3, a4, a5, a6, a7}), yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
        case D2.GKArr{}:
          M3.no({sc.fin(sc.run(D2.g.text(D2.GNextM{a1, a2, a3, a4, a5, a6, a7}), yy)) == SOut{LVal{}, dd} : Sc}, h_ok)
        case D2.GKObj{}:
          hv = Equal.trans(Sc, sc.fin(yy), SOut{lt, dd}, SOut{LVal{}, dd}, hy, Equal.cong(Lt, Sc, zz => SOut{zz, dd},
            lt, LVal{}, lv_eq(lt, h_lt)))
          tr(",", a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++ D2.g.text(a7),
            yy, SOut{LSt{}, dd}, SOut{LVal{}, dd}, p_ch(',', {==}, SOut{LVal{}, dd}, yy, hv), +y0 => e0 => tr(a1,
            "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++ D2.g.text(a7), y0,
            SOut{LSt{}, dd}, SOut{LVal{}, dd}, p_ws(a1, M3.and_left(D1.all_ws(a1), Bool.and(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h_ok), LSt{}, dd, y0, e0),
            +y1 => e1 => tr("\"",
            D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++ D2.g.text(a7), y1, SIn{dd},
            SOut{LVal{}, dd}, p_ch('"', {==}, SOut{LSt{}, dd}, y1, e1), +y2 => e2 => tr(D2.spell(a2),
            "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++ D2.g.text(a7), y2, SIn{dd}, SOut{LVal{}, dd},
            p_sp(a2, M3.and_left(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))),
            M3.and_right(D1.all_ws(a1), Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h_ok)),
            dd, y2, e2), +y3 => e3 => tr("\"", a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++ D2.g.text(a7), y3,
            SOut{LVal{}, dd}, SOut{LVal{}, dd}, p_ch('"', {==}, SIn{dd}, y3, e3), +y4 => e4 => tr(a3,
            ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++ D2.g.text(a7), y4, SOut{LVal{}, dd}, SOut{LVal{}, dd}, p_ws(a3,
            M3.and_left(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M3.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M3.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h_ok))), LVal{}, dd, y4, e4),
            +y5 => e5 => tr(":", a4 ++ D2.g.text(a5) ++ a6 ++ D2.g.text(a7), y5, SOut{LSt{}, dd}, SOut{LVal{}, dd},
            p_ch(':', {==}, SOut{LVal{}, dd}, y5, e5), +y6 => e6 => tr(a4, D2.g.text(a5) ++ a6 ++ D2.g.text(a7),
            y6, SOut{LSt{}, dd}, SOut{LVal{}, dd}, p_ws(a4, M3.and_left(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))), M3.and_right(D1.all_ws(a3),
            Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{})))), M3.and_right(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))),
            M3.and_right(D1.all_ws(a1), Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h_ok)))),
            LSt{}, dd, y6, e6), +y7 => e7 => tr(D2.g.text(a5), a6 ++ D2.g.text(a7), y7, SOut{LVal{}, dd},
            SOut{LVal{}, dd}, g1(a5, D2.GKVal{}, M3.and_left(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6),
            D2.g.ok(a7, D2.GKObj{})), M3.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))), M3.and_right(D1.all_ws(a3),
            Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{})))), M3.and_right(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))),
            M3.and_right(D1.all_ws(a1), Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))),
            h_ok))))), LSt{}, dd, {==}, y7, e7), +y8 => e8 => tr(a6, D2.g.text(a7), y8, SOut{LVal{}, dd},
            SOut{LVal{}, dd}, p_ws(a6, M3.and_left(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}), M3.and_right(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})), M3.and_right(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))),
            M3.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M3.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M3.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h_ok)))))), LVal{}, dd, y8, e8),
            +y9 => e9 => g1(a7, D2.GKObj{}, M3.and_right(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}),
            M3.and_right(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})),
            M3.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{}))), M3.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M3.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M3.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h_ok)))))), LVal{}, dd, {==},
            y9, e9)))))))))))
