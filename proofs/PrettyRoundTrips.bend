# proofs of laws/PrettyRoundTrips.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../src/lazy.bend as Lazy
import ../src/print.bend as Print
import ../laws/NumOkIsNumberRule.bend as L1
import ../laws/ParsesExactlyJsonTexts.bend as L2
import ../laws/PrettyRoundTrips.bend as Laws
import ../laws/defs/CursorAndNumberRules.bend as D1
import ../laws/defs/GrammarDerivations.bend as D2
import ./lemmas/ArrayLength.bend as M1
import ./lemmas/CursorFollowsDerivation.bend as M2
import ./lemmas/DerivationText.bend as M3
import ./lemmas/LexemeOrder.bend as M4
import ./lemmas/NumberDigits.bend as M5
import ./lemmas/ParserReadsTokens.bend as M6
import ./lemmas/WellFormedCells.bend as M7

# laws/PrettyRoundTrips.bend: pretty's text is a derivation of RFC 8259's value rule, so
# text_some reads it back. First the pieces print writes, one character at a
# time.

# the piece for a control below U+0020, or the character itself
def pq.rest(+uu: U32, bc: Bool) -> D2.Piece:
  match bc:
    case True{}:
      D2.PU{'0', '0', Print.escape.nib(U32.div(uu, 16)), Print.escape.nib(U32.mod(uu, 16))}
    case False{}:
      D2.PRaw{Chr{uu}}

# the piece print writes for a scalar value, one test of escape.plain at a
# time
def pq.pl(
  +uu: U32,
  b34: Bool,
  b92: Bool,
  b8: Bool,
  b12: Bool,
  b10: Bool,
  b13: Bool,
  b9: Bool,
  bc: Bool
) -> D2.Piece:
  match b34:
    case True{}:
      D2.PEsc{'"'}
    case False{}:
      match b92:
        case True{}:
          D2.PEsc{'\\'}
        case False{}:
          match b8:
            case True{}:
              D2.PEsc{'b'}
            case False{}:
              match b12:
                case True{}:
                  D2.PEsc{'f'}
                case False{}:
                  match b10:
                    case True{}:
                      D2.PEsc{'n'}
                    case False{}:
                      match b13:
                        case True{}:
                          D2.PEsc{'r'}
                        case False{}:
                          match b9:
                            case True{}:
                              D2.PEsc{'t'}
                            case False{}:
                              pq.rest(uu, bc)

# the piece print writes for a code point: U+FFFD for one that is not a
# scalar value
def pq.sc(+uu: U32, ns: Bool) -> D2.Piece:
  match ns:
    case True{}:
      D2.PRaw{Char.from_u32(65533)}
    case False{}:
      pq.pl(uu, U32.is_eq(uu, 34), U32.is_eq(uu, 92), U32.is_eq(uu, 8), U32.is_eq(uu, 12), U32.is_eq(uu, 10),
        U32.is_eq(uu, 13), U32.is_eq(uu, 9), U32.is_lt(uu, 32))

# the piece print writes for a character
def pq.pc(ch: Char) -> D2.Piece:
  match ch:
    case Chr{+uu}:
      pq.sc(uu, D1.non_scalar(uu))

# the pieces print writes for a string
def pq.pcs(txt: String) -> List<&2, D2.Piece>:
  match txt:
    case SNil{}:
      []
    case SCon{hd, tl}:
      pq.pc(hd) <> pq.pcs(tl)

# pq.pl is written as escape.plain writes, test for test
law pq.pl_text:
  for +uu: U32
  for b34: Bool
  for b92: Bool
  for b8: Bool
  for b12: Bool
  for b10: Bool
  for b13: Bool
  for b9: Bool
  for bc: Bool
  {D2.piece.text(pq.pl(uu, b34, b92, b8, b12, b10, b13, b9, bc)) == Bool.pick(String, b34, "\\\"",
    Bool.pick(String, b92, "\\\\", Bool.pick(String, b8, "\\b", Bool.pick(String, b12, "\\f",
    Bool.pick(String, b10, "\\n", Bool.pick(String, b13, "\\r", Bool.pick(String, b9, "\\t",
    Print.escape.rest.go(uu, Chr{uu}, bc)))))))) : String}

def pq.pl_text(_uu, b34, b92, b8, b12, b10, b13, b9, bc):
  match b34:
    case True{}:
      {==}
    case False{}:
      match b92:
        case True{}:
          {==}
        case False{}:
          match b8:
            case True{}:
              {==}
            case False{}:
              match b12:
                case True{}:
                  {==}
                case False{}:
                  match b10:
                    case True{}:
                      {==}
                    case False{}:
                      match b13:
                        case True{}:
                          {==}
                        case False{}:
                          match b9:
                            case True{}:
                              {==}
                            case False{}:
                              match bc:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}

# pq.sc is written as escape.scalar writes
law pq.sc_text:
  for +uu: U32
  for ns: Bool
  {D2.piece.text(pq.sc(uu, ns)) == Print.escape.scalar(uu, Chr{uu}, Bool.not(ns)) : String}

def pq.sc_text(uu, ns):
  match ns:
    case True{}:
      {==}
    case False{}:
      pq.pl_text(uu, U32.is_eq(uu, 34), U32.is_eq(uu, 92), U32.is_eq(uu, 8), U32.is_eq(uu, 12), U32.is_eq(uu, 10),
        U32.is_eq(uu, 13), U32.is_eq(uu, 9), U32.is_lt(uu, 32))

# a character's piece is written as print writes the character
law pq.pc_text:
  for +ch: Char
  {D2.piece.text(pq.pc(ch)) == Print.escape.char(ch) : String}

def pq.pc_text(ch):
  match ch:
    case Chr{+uu}:
      pq.sc_text(uu, D1.non_scalar(uu))

# a string's pieces are written as print escapes the string
law pq.pcs_text:
  for +txt: String
  {D2.spell(pq.pcs(txt)) == Print.escape(String.to_list(txt)) : String}

def pq.pcs_text(txt):
  match txt:
    case SNil{}:
      {==}
    case SCon{+hd, +tl}:
      Equal.trans(String, D2.piece.text(pq.pc(hd)) ++ D2.spell(pq.pcs(tl)),
        Print.escape.char(hd) ++ D2.spell(pq.pcs(tl)), Print.escape.char(hd) ++ Print.escape(String.to_list(tl)),
        Equal.cong(String, String, zz => zz ++ D2.spell(pq.pcs(tl)), D2.piece.text(pq.pc(hd)),
          Print.escape.char(hd), pq.pc_text(hd)),
        Equal.cong(String, String, zz => Print.escape.char(hd) ++ zz, D2.spell(pq.pcs(tl)),
          Print.escape(String.to_list(tl)), pq.pcs_text(tl)))

# a control's \u00XX piece stands for the control
def pq.ctl_char.goal(uu: U32) -> Type:
  {D2.piece.char(D2.PU{'0', '0', Print.escape.nib(U32.div(uu, 16)), Print.escape.nib(U32.mod(uu,
    16))}) == Chr{uu} : Char}

# pq.ctl_char, one control at a time
law pq.ctl_char.five:
  for b0: Bool
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  {D2.piece.char(D2.PU{'0', '0', Print.escape.nib(U32.div(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4,
    WCon{False{}, M7.zw(26n)}}}}}}}, 16)), Print.escape.nib(U32.mod(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4,
    WCon{False{}, M7.zw(26n)}}}}}}}, 16))}) == Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{},
    M7.zw(26n)}}}}}}}} : Char}

def pq.ctl_char.five(b0, b1, b2, b3, b4):
  match b0 b1 b2 b3 b4:
    case False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{}:
      {==}

# pq.ctl_char, once bit 5 and the bits above are known
law pq.ctl_char.at:
  for cc: Cmp
  for b5: Bool
  for b0: Bool
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  for +rest: Word(26n)
  for ec: {Word.cmp(26n, rest, M7.zw(26n)) == cc : Cmp}
  for h_lt: {Cmp.is_lt(Word.cmp.fin(b5, True{}, cc)) == True{} : Bool}
  {D2.piece.char(D2.PU{'0', '0', Print.escape.nib(U32.div(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5,
    rest}}}}}}}, 16)), Print.escape.nib(U32.mod(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}},
    16))}) == Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}} : Char}

def pq.ctl_char.at(cc, b5, b0, b1, b2, b3, b4, rest, ec, h_lt):
  match cc:
    case LT{}:
      ez = Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Word.cmp(26n, rest, M7.zw(26n)), LT{}, ec)
      Empty.absurd(pq.ctl_char.goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}),
        M1.true_false(Equal.trans(Bool, True{}, Cmp.is_lt(Word.cmp(26n, rest, M7.zw(26n))), False{},
        Equal.sym(Bool, Cmp.is_lt(Word.cmp(26n, rest, M7.zw(26n))), True{}, ez), M7.zw_nlt(26n, rest))))
    case GT{}:
      match b5:
        case False{}:
          Empty.absurd(pq.ctl_char.goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}),
            M4.false_true(h_lt))
        case True{}:
          Empty.absurd(pq.ctl_char.goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}),
            M4.false_true(h_lt))
    case EQ{}:
      match b5:
        case True{}:
          Empty.absurd(pq.ctl_char.goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}),
            M4.false_true(h_lt))
        case False{}:
          er = Equal.sym(Word(26n), rest, M7.zw(26n),
            M7.weq(26n, rest, M7.zw(26n), Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(26n, rest, M7.zw(26n)),
                EQ{}, ec)))
          %er : {D2.piece.char(D2.PU{'0', '0', Print.escape.nib(U32.div(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
            WCon{b4, WCon{False{}, _}}}}}}}, 16)), Print.escape.nib(U32.mod(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
            WCon{b4, WCon{False{}, _}}}}}}}, 16))}) == Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4,
            WCon{False{}, _}}}}}}}} : Char}
          pq.ctl_char.five(b0, b1, b2, b3, b4)

# a control's \u00XX piece stands for the control
law pq.ctl_char:
  for +uu: U32
  for h_lt: {U32.is_lt(uu, 32) == True{} : Bool}
  {D2.piece.char(D2.PU{'0', '0', Print.escape.nib(U32.div(uu, 16)), Print.escape.nib(U32.mod(uu,
    16))}) == Chr{uu} : Char}

def pq.ctl_char(uu, h_lt):
  match uu:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, +rest}}}}}}}:
      +c5 = Word.cmp.fin(b5, True{}, Word.cmp(26n, rest, M7.zw(26n)))
      +c4 = Word.cmp.fin(b4, False{}, c5)
      +c3 = Word.cmp.fin(b3, False{}, c4)
      +c2 = Word.cmp.fin(b2, False{}, c3)
      +c1 = Word.cmp.fin(b1, False{}, c2)
      h5 = M7.lt_up(b4, c5, M7.lt_up(b3, c4, M7.lt_up(b2, c3, M7.lt_up(b1, c2, M7.lt_up(b0, c1, h_lt)))))
      pq.ctl_char.at(Word.cmp(26n, rest, M7.zw(26n)), b5, b0, b1, b2, b3, b4, rest, {==}, h5)

# a control's \u00XX piece is well spelled
def pq.ctl_ok.goal(uu: U32) -> Type:
  {D2.piece.ok(D2.PU{'0', '0', Print.escape.nib(U32.div(uu, 16)), Print.escape.nib(U32.mod(uu,
    16))}) == True{} : Bool}

# pq.ctl_ok, one control at a time
law pq.ctl_ok.five:
  for b0: Bool
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  {D2.piece.ok(D2.PU{'0', '0', Print.escape.nib(U32.div(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4,
    WCon{False{}, M7.zw(26n)}}}}}}}, 16)), Print.escape.nib(U32.mod(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4,
    WCon{False{}, M7.zw(26n)}}}}}}}, 16))}) == True{} : Bool}

def pq.ctl_ok.five(b0, b1, b2, b3, b4):
  match b0 b1 b2 b3 b4:
    case False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{}:
      {==}

# pq.ctl_ok, once bit 5 and the bits above are known
law pq.ctl_ok.at:
  for cc: Cmp
  for b5: Bool
  for b0: Bool
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  for +rest: Word(26n)
  for ec: {Word.cmp(26n, rest, M7.zw(26n)) == cc : Cmp}
  for h_lt: {Cmp.is_lt(Word.cmp.fin(b5, True{}, cc)) == True{} : Bool}
  {D2.piece.ok(D2.PU{'0', '0', Print.escape.nib(U32.div(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5,
    rest}}}}}}}, 16)), Print.escape.nib(U32.mod(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}},
    16))}) == True{} : Bool}

def pq.ctl_ok.at(cc, b5, b0, b1, b2, b3, b4, rest, ec, h_lt):
  match cc:
    case LT{}:
      ez = Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Word.cmp(26n, rest, M7.zw(26n)), LT{}, ec)
      Empty.absurd(pq.ctl_ok.goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}),
        M1.true_false(Equal.trans(Bool, True{}, Cmp.is_lt(Word.cmp(26n, rest, M7.zw(26n))), False{},
        Equal.sym(Bool, Cmp.is_lt(Word.cmp(26n, rest, M7.zw(26n))), True{}, ez), M7.zw_nlt(26n, rest))))
    case GT{}:
      match b5:
        case False{}:
          Empty.absurd(pq.ctl_ok.goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}),
            M4.false_true(h_lt))
        case True{}:
          Empty.absurd(pq.ctl_ok.goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}),
            M4.false_true(h_lt))
    case EQ{}:
      match b5:
        case True{}:
          Empty.absurd(pq.ctl_ok.goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}),
            M4.false_true(h_lt))
        case False{}:
          er = Equal.sym(Word(26n), rest, M7.zw(26n),
            M7.weq(26n, rest, M7.zw(26n), Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(26n, rest, M7.zw(26n)),
                EQ{}, ec)))
          %er : {D2.piece.ok(D2.PU{'0', '0', Print.escape.nib(U32.div(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
            WCon{b4, WCon{False{}, _}}}}}}}, 16)), Print.escape.nib(U32.mod(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3,
            WCon{b4, WCon{False{}, _}}}}}}}, 16))}) == True{} : Bool}
          pq.ctl_ok.five(b0, b1, b2, b3, b4)

# a control's \u00XX piece is well spelled
law pq.ctl_ok:
  for +uu: U32
  for h_lt: {U32.is_lt(uu, 32) == True{} : Bool}
  {D2.piece.ok(D2.PU{'0', '0', Print.escape.nib(U32.div(uu, 16)), Print.escape.nib(U32.mod(uu,
    16))}) == True{} : Bool}

def pq.ctl_ok(uu, h_lt):
  match uu:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, +rest}}}}}}}:
      +c5 = Word.cmp.fin(b5, True{}, Word.cmp(26n, rest, M7.zw(26n)))
      +c4 = Word.cmp.fin(b4, False{}, c5)
      +c3 = Word.cmp.fin(b3, False{}, c4)
      +c2 = Word.cmp.fin(b2, False{}, c3)
      +c1 = Word.cmp.fin(b1, False{}, c2)
      h5 = M7.lt_up(b4, c5, M7.lt_up(b3, c4, M7.lt_up(b2, c3, M7.lt_up(b1, c2, M7.lt_up(b0, c1, h_lt)))))
      pq.ctl_ok.at(Word.cmp(26n, rest, M7.zw(26n)), b5, b0, b1, b2, b3, b4, rest, {==}, h5)

# a scalar value's piece stands for the value
law pq.pl_char:
  for +uu: U32
  for b34: Bool
  for b92: Bool
  for b8: Bool
  for b12: Bool
  for b10: Bool
  for b13: Bool
  for b9: Bool
  for bc: Bool
  for e34: {U32.is_eq(uu, 34) == b34 : Bool}
  for e92: {U32.is_eq(uu, 92) == b92 : Bool}
  for e8: {U32.is_eq(uu, 8) == b8 : Bool}
  for e12: {U32.is_eq(uu, 12) == b12 : Bool}
  for e10: {U32.is_eq(uu, 10) == b10 : Bool}
  for e13: {U32.is_eq(uu, 13) == b13 : Bool}
  for e9: {U32.is_eq(uu, 9) == b9 : Bool}
  for ec: {U32.is_lt(uu, 32) == bc : Bool}
  {D2.piece.char(pq.pl(uu, b34, b92, b8, b12, b10, b13, b9, bc)) == Chr{uu} : Char}

def pq.pl_char(uu, b34, b92, b8, b12, b10, b13, b9, bc, e34, e92, e8, e12, e10, e13, e9, ec):
  match b34:
    case True{}:
      Equal.sym(Char, Chr{uu}, Chr{34}, Equal.cong(U32, Char, xx => Chr{xx}, uu, 34, M7.ueq(uu, 34, e34)))
    case False{}:
      match b92:
        case True{}:
          Equal.sym(Char, Chr{uu}, Chr{92}, Equal.cong(U32, Char, xx => Chr{xx}, uu, 92, M7.ueq(uu, 92, e92)))
        case False{}:
          match b8:
            case True{}:
              Equal.sym(Char, Chr{uu}, Chr{8}, Equal.cong(U32, Char, xx => Chr{xx}, uu, 8, M7.ueq(uu, 8, e8)))
            case False{}:
              match b12:
                case True{}:
                  Equal.sym(Char, Chr{uu}, Chr{12}, Equal.cong(U32, Char, xx => Chr{xx}, uu, 12, M7.ueq(uu, 12, e12)))
                case False{}:
                  match b10:
                    case True{}:
                      Equal.sym(Char, Chr{uu}, Chr{10}, Equal.cong(U32, Char, xx => Chr{xx}, uu, 10, M7.ueq(uu, 10,
                          e10)))
                    case False{}:
                      match b13:
                        case True{}:
                          Equal.sym(Char, Chr{uu}, Chr{13}, Equal.cong(U32, Char, xx => Chr{xx}, uu, 13, M7.ueq(uu, 13,
                            e13)))
                        case False{}:
                          match b9:
                            case True{}:
                              Equal.sym(Char, Chr{uu}, Chr{9}, Equal.cong(U32, Char, xx => Chr{xx}, uu, 9, M7.ueq(uu, 9,
                                e9)))
                            case False{}:
                              match bc:
                                case True{}:
                                  pq.ctl_char(uu, ec)
                                case False{}:
                                  {==}

# a scalar value's piece is well spelled
law pq.pl_ok:
  for +uu: U32
  for b34: Bool
  for b92: Bool
  for b8: Bool
  for b12: Bool
  for b10: Bool
  for b13: Bool
  for b9: Bool
  for bc: Bool
  for e34: {U32.is_eq(uu, 34) == b34 : Bool}
  for e92: {U32.is_eq(uu, 92) == b92 : Bool}
  for e8: {U32.is_eq(uu, 8) == b8 : Bool}
  for e12: {U32.is_eq(uu, 12) == b12 : Bool}
  for e10: {U32.is_eq(uu, 10) == b10 : Bool}
  for e13: {U32.is_eq(uu, 13) == b13 : Bool}
  for e9: {U32.is_eq(uu, 9) == b9 : Bool}
  for ec: {U32.is_lt(uu, 32) == bc : Bool}
  {D2.piece.ok(pq.pl(uu, b34, b92, b8, b12, b10, b13, b9, bc)) == True{} : Bool}

def pq.pl_ok(uu, b34, b92, b8, b12, b10, b13, b9, bc, e34, e92, _e8, _e12, _e10, _e13, _e9, ec):
  match b34:
    case True{}:
      {==}
    case False{}:
      match b92:
        case True{}:
          {==}
        case False{}:
          match b8:
            case True{}:
              {==}
            case False{}:
              match b12:
                case True{}:
                  {==}
                case False{}:
                  match b10:
                    case True{}:
                      {==}
                    case False{}:
                      match b13:
                        case True{}:
                          {==}
                        case False{}:
                          match b9:
                            case True{}:
                              {==}
                            case False{}:
                              match bc:
                                case True{}:
                                  pq.ctl_ok(uu, ec)
                                case False{}:
                                  s34 = Equal.sym(Bool, U32.is_eq(uu, 34), False{}, e34)
                                  s92 = Equal.sym(Bool, U32.is_eq(uu, 92), False{}, e92)
                                  sc = Equal.sym(Bool, U32.is_lt(uu, 32), False{}, ec)
                                  %s34 : {Bool.not(Bool.or(_, Bool.or(U32.is_eq(uu, 92), U32.is_lt(uu,
                                    32)))) == True{} : Bool}
                                  %s92 : {Bool.not(Bool.or(False{}, Bool.or(_, U32.is_lt(uu, 32)))) == True{} : Bool}
                                  %sc : {Bool.not(Bool.or(False{}, Bool.or(False{}, _))) == True{} : Bool}
                                  {==}

# a code point's piece stands for it as print writes it
law pq.sc_char:
  for +uu: U32
  for ns: Bool
  {D2.piece.char(pq.sc(uu, ns)) == Bool.pick(Char, ns, Char.from_u32(65533), Chr{uu}) : Char}

def pq.sc_char(uu, ns):
  match ns:
    case True{}:
      {==}
    case False{}:
      pq.pl_char(uu, U32.is_eq(uu, 34), U32.is_eq(uu, 92), U32.is_eq(uu, 8), U32.is_eq(uu, 12), U32.is_eq(uu, 10),
        U32.is_eq(uu, 13), U32.is_eq(uu, 9), U32.is_lt(uu, 32),
        {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a code point's piece is well spelled
law pq.sc_ok:
  for +uu: U32
  for ns: Bool
  {D2.piece.ok(pq.sc(uu, ns)) == True{} : Bool}

def pq.sc_ok(uu, ns):
  match ns:
    case True{}:
      {==}
    case False{}:
      pq.pl_ok(uu, U32.is_eq(uu, 34), U32.is_eq(uu, 92), U32.is_eq(uu, 8), U32.is_eq(uu, 12), U32.is_eq(uu, 10),
        U32.is_eq(uu, 13), U32.is_eq(uu, 9), U32.is_lt(uu, 32),
        {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a character's piece stands for the character as print writes it
law pq.pc_char:
  for +ch: Char
  {D2.piece.char(pq.pc(ch)) == D1.fix_char(ch) : Char}

def pq.pc_char(ch):
  match ch:
    case Chr{+uu}:
      pq.sc_char(uu, D1.non_scalar(uu))

# a character's piece is well spelled
law pq.pc_ok:
  for +ch: Char
  {D2.piece.ok(pq.pc(ch)) == True{} : Bool}

def pq.pc_ok(ch):
  match ch:
    case Chr{+uu}:
      pq.sc_ok(uu, D1.non_scalar(uu))

# a string's pieces stand for the string as print writes it
law pq.pcs_spelled:
  for +txt: String
  {D2.spelled(pq.pcs(txt)) == D1.fix_str(txt) : String}

def pq.pcs_spelled(txt):
  match txt:
    case SNil{}:
      {==}
    case SCon{+hd, +tl}:
      Equal.trans(String, SCon{D2.piece.char(pq.pc(hd)), D2.spelled(pq.pcs(tl))},
        SCon{D1.fix_char(hd), D2.spelled(pq.pcs(tl))}, SCon{D1.fix_char(hd), D1.fix_str(tl)},
        Equal.cong(Char, String, zz => SCon{zz, D2.spelled(pq.pcs(tl))}, D2.piece.char(pq.pc(hd)),
          D1.fix_char(hd), pq.pc_char(hd)),
        Equal.cong(String, String, zz => SCon{D1.fix_char(hd), zz}, D2.spelled(pq.pcs(tl)), D1.fix_str(tl),
          pq.pcs_spelled(tl)))

# a string's pieces are well spelled
law pq.pcs_ok:
  for +txt: String
  {D2.spell_ok(pq.pcs(txt)) == True{} : Bool}

def pq.pcs_ok(txt):
  match txt:
    case SNil{}:
      {==}
    case SCon{+hd, +tl}:
      eh = Equal.sym(Bool, D2.piece.ok(pq.pc(hd)), True{}, pq.pc_ok(hd))
      et = Equal.sym(Bool, D2.spell_ok(pq.pcs(tl)), True{}, pq.pcs_ok(tl))
      %eh : {Bool.and(_, D2.spell_ok(pq.pcs(tl))) == True{} : Bool}
      %et : {Bool.and(True{}, _) == True{} : Bool}
      {==}

# Second, a derivation of pretty's text, built from the value. The
# whitespace after an element or member is `close` when it is the last
def pq.w(tl: V.Json, +close: String) -> String:
  match tl:
    case V.JNil{}:
      close
    case _:
      ""

# a derivation whose text is pretty.go's: a newline and `ind` start each
# element or member of a chain of cells, and `close` follows the last one
def pq.g(val: V.Json, +ind: String, +close: String) -> D2.Gv:
  match val:
    case V.JNull{}:
      D2.GWord{"null"}
    case V.JBool{True{}}:
      D2.GWord{"true"}
    case V.JBool{False{}}:
      D2.GWord{"false"}
    case V.JNum{raw}:
      D2.GWord{raw}
    case V.JStr{s}:
      D2.GStr{pq.pcs(s)}
    case V.JSpan{src, +n}:
      D2.GStr{pq.pcs(V.span.str(src, n, U32.is_zero(n)))}
    case V.JArr{V.JCons{h, +t}}:
      +inner = "  " ++ ind
      D2.GArr{"\n" ++ inner, pq.g(h, inner, ""), pq.w(t, "\n" ++ ind), pq.g(t, inner, "\n" ++ ind)}
    case V.JArr{_}:
      D2.GArr0{""}
    case V.JObj{V.JPair{k, v, +r}}:
      +inner = "  " ++ ind
      D2.GObj{"\n" ++ inner, pq.pcs(k), "", " ", pq.g(v, inner, ""), pq.w(r, "\n" ++ ind), pq.g(r, inner,
        "\n" ++ ind)}
    case V.JObj{V.JBind{src, +n, v, +r}}:
      +inner = "  " ++ ind
      D2.GObj{"\n" ++ inner, pq.pcs(V.span.str(src, n, U32.is_zero(n))), "", " ", pq.g(v, inner, ""),
        pq.w(r, "\n" ++ ind), pq.g(r, inner, "\n" ++ ind)}
    case V.JObj{_}:
      D2.GObj0{""}
    case V.JNil{}:
      D2.GEnd{}
    case V.JCons{h, +t}:
      D2.GNext{"\n" ++ ind, pq.g(h, ind, ""), pq.w(t, close), pq.g(t, ind, close)}
    case V.JPair{k, v, +r}:
      D2.GNextM{"\n" ++ ind, pq.pcs(k), "", " ", pq.g(v, ind, ""), pq.w(r, close), pq.g(r, ind, close)}
    case V.JBind{src, +n, v, +r}:
      D2.GNextM{"\n" ++ ind, pq.pcs(V.span.str(src, n, U32.is_zero(n))), "", " ", pq.g(v, ind, ""), pq.w(r, close),
        pq.g(r, ind, close)}

# the text of a chain of cells in front of a tail, from its first element or
# member on, grouped to the right as gt groups it
def pq.ct(val: V.Json, +ind: String, +close: String, tail: String) -> String:
  match val:
    case V.JCons{h, +t}:
      M3.gt(pq.g(h, ind, ""), pq.w(t, close) ++ M3.gt(pq.g(t, ind, close), tail))
    case V.JPair{k, v, +r}:
      SCon{'"', M1.sp(pq.pcs(k), SCon{'"', "" ++ SCon{':', " " ++ M3.gt(pq.g(v, ind, ""), pq.w(r,
          close) ++ M3.gt(pq.g(r,
        ind, close), tail))}})}
    case V.JBind{src, +n, v, +r}:
      SCon{'"', M1.sp(pq.pcs(V.span.str(src, n, U32.is_zero(n))), SCon{'"', "" ++ SCon{':', " " ++ M3.gt(pq.g(v, ind,
          ""),
        pq.w(r, close) ++ M3.gt(pq.g(r, ind, close), tail))}})}
    case _:
      tail

# what pretty.go's text in front of a tail is: a value's derivation, or a
# chain's cells
def pq.tx(val: V.Json, +ind: String, +close: String, sh: V.Shape, tail: String) -> String:
  match sh:
    case V.WVal{}:
      M3.gt(pq.g(val, ind, close), tail)
    case _:
      pq.ct(val, ind, close, tail)

# the claim pq.tl makes of one value or chain
def pq.goal(val: V.Json, ind: String, close: String, sh: V.Shape, tail: String) -> Type:
  {Print.pretty.go(val, ind, close) ++ tail == pq.tx(val, ind, close, sh, tail) : String}

# print's escaped string in front of a quotation mark is the string's pieces
law pq.q:
  for +txt: String
  for +tail: String
  {Print.escape(String.to_list(txt)) ++ SCon{'"', tail} == M1.sp(pq.pcs(txt), SCon{'"', tail}) : String}

def pq.q(txt, tail):
  Equal.trans(String, Print.escape(String.to_list(txt)) ++ SCon{'"', tail}, D2.spell(pq.pcs(txt)) ++ SCon{'"', tail},
    M1.sp(pq.pcs(txt), SCon{'"', tail}),
    Equal.cong(String, String, zz => zz ++ SCon{'"', tail}, Print.escape(String.to_list(txt)), D2.spell(pq.pcs(txt)),
      Equal.sym(String, D2.spell(pq.pcs(txt)), Print.escape(String.to_list(txt)), pq.pcs_text(txt))),
    M3.sp_eq(pq.pcs(txt), SCon{'"', tail}))

# a quoted string in front of a tail
law pq.qt:
  for +txt: String
  for +tail: String
  {Print.quote(txt) ++ tail == SCon{'"', M1.sp(pq.pcs(txt), SCon{'"', tail})} : String}

def pq.qt(txt, tail):
  Equal.cong(String, String, zz => SCon{'"', zz}, (Print.escape(String.to_list(txt)) ++ "\"") ++ tail,
    M1.sp(pq.pcs(txt), SCon{'"', tail}),
    M3.app3(Print.escape(String.to_list(txt)), "\"", tail, SCon{'"', tail}, M1.sp(pq.pcs(txt), SCon{'"', tail}), {==},
      pq.q(txt, tail)))

# a member's name, then the rest, in front of a tail
law pq.mem:
  for +txt: String
  for +mm: String
  for +tail: String
  for +qq: String
  for em: {mm ++ tail == qq : String}
  {(Print.quote(txt) ++ mm) ++ tail == SCon{'"', M1.sp(pq.pcs(txt), SCon{'"', qq})} : String}

def pq.mem(txt, mm, tail, qq, em):
  Equal.trans(String, (Print.quote(txt) ++ mm) ++ tail, Print.quote(txt) ++ (mm ++ tail),
    SCon{'"', M1.sp(pq.pcs(txt), SCon{'"', qq})}, M2.sassoc(Print.quote(txt), mm, tail),
    Equal.trans(String, Print.quote(txt) ++ (mm ++ tail), Print.quote(txt) ++ qq,
      SCon{'"', M1.sp(pq.pcs(txt), SCon{'"', qq})},
      Equal.cong(String, String, zz => Print.quote(txt) ++ zz, mm ++ tail, qq, em), pq.qt(txt, qq)))

# an element or member that is not the last: its text, a comma, `ind` and the
# rest, in front of a tail
law pq.cell:
  for +aa: String
  for +ind: String
  for +rr: String
  for +tail: String
  for +cc: String
  for +gg: String
  for er: {rr ++ tail == cc : String}
  for eh: {aa ++ SCon{',', ind ++ cc} == gg : String}
  {(aa ++ ("," ++ (ind ++ rr))) ++ tail == gg : String}

def pq.cell(aa, ind, rr, tail, cc, gg, er, eh):
  M3.app3(aa, "," ++ (ind ++ rr), tail, SCon{',', ind ++ cc}, gg,
    Equal.cong(String, String, zz => SCon{',', zz}, (ind ++ rr) ++ tail, ind ++ cc, M3.app3(ind, rr, tail, cc,
        ind ++ cc,
      er, {==})), eh)

# the last element or member: its text and `close`, in front of a tail
law pq.last:
  for +aa: String
  for +close: String
  for +tail: String
  for +gg: String
  for eh: {aa ++ (close ++ tail) == gg : String}
  {(aa ++ close) ++ tail == gg : String}

def pq.last(aa, close, tail, gg, eh):
  M3.app3(aa, close, tail, close ++ tail, gg, {==}, eh)

# a container's inside and its closing bracket, in front of a tail
law pq.wrap:
  for +inner: String
  for +pp: String
  for +br: Char
  for +tail: String
  for +cc: String
  for ep: {pp ++ SCon{br, tail} == cc : String}
  {(inner ++ (pp ++ SCon{br, ""})) ++ tail == inner ++ cc : String}

def pq.wrap(inner, pp, br, tail, cc, ep):
  M3.app3(inner, pp ++ SCon{br, ""}, tail, cc, inner ++ cc, M3.app3(pp, SCon{br, ""}, tail, SCon{br, tail}, cc, {==},
      ep),
    {==})

# the left side of a Lazy.stop that wf.go takes as an and
law pq.left:
  for aa: Bool
  for -bb: Bool
  for h: {Lazy.stop(Bool, Bool.not(aa), False{}, _u => bb) == True{} : Bool}
  {aa == True{} : Bool}

def pq.left(aa, _bb, h):
  match aa:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, M4.false_true(h))

# the right side of a Lazy.stop that wf.go takes as an and
law pq.right:
  for aa: Bool
  for -bb: Bool
  for h: {Lazy.stop(Bool, Bool.not(aa), False{}, _u => bb) == True{} : Bool}
  {bb == True{} : Bool}

def pq.right(aa, bb, h):
  match aa:
    case True{}:
      h
    case False{}:
      Empty.absurd({bb == True{} : Bool}, M4.false_true(h))

# pretty.go's text in front of a tail is the derivation's, for a
# well-formed value or chain
law pq.tl:
  for +val: V.Json
  for +ind: String
  for +close: String
  for sh: V.Shape
  for +tail: String
  for +h: {V.wf.go(val, sh) == True{} : Bool}
  {Print.pretty.go(val, ind, close) ++ tail == pq.tx(val, ind, close, sh, tail) : String}

def pq.tl(val, ind, close, sh, tail, h):
  match val sh:
    case V.JNull{} V.WVal{}:
      {==}
    case V.JNull{} V.WArr{}:
      Empty.absurd(pq.goal(V.JNull{}, ind, close, V.WArr{}, tail), M4.false_true(h))
    case V.JNull{} V.WObj{}:
      Empty.absurd(pq.goal(V.JNull{}, ind, close, V.WObj{}, tail), M4.false_true(h))
    case V.JBool{True{}} V.WVal{}:
      {==}
    case V.JBool{False{}} V.WVal{}:
      {==}
    case V.JBool{bl} V.WArr{}:
      Empty.absurd(pq.goal(V.JBool{bl}, ind, close, V.WArr{}, tail), M4.false_true(h))
    case V.JBool{bl} V.WObj{}:
      Empty.absurd(pq.goal(V.JBool{bl}, ind, close, V.WObj{}, tail), M4.false_true(h))
    case V.JNum{raw} V.WVal{}:
      {==}
    case V.JNum{raw} V.WArr{}:
      Empty.absurd(pq.goal(V.JNum{raw}, ind, close, V.WArr{}, tail), M4.false_true(h))
    case V.JNum{raw} V.WObj{}:
      Empty.absurd(pq.goal(V.JNum{raw}, ind, close, V.WObj{}, tail), M4.false_true(h))
    case V.JStr{+s} V.WVal{}:
      pq.qt(s, tail)
    case V.JStr{s} V.WArr{}:
      Empty.absurd(pq.goal(V.JStr{s}, ind, close, V.WArr{}, tail), M4.false_true(h))
    case V.JStr{s} V.WObj{}:
      Empty.absurd(pq.goal(V.JStr{s}, ind, close, V.WObj{}, tail), M4.false_true(h))
    case V.JSpan{src, +n} V.WVal{}:
      pq.qt(V.span.str(src, n, U32.is_zero(n)), tail)
    case V.JSpan{src, n} V.WArr{}:
      Empty.absurd(pq.goal(V.JSpan{src, n}, ind, close, V.WArr{}, tail), M4.false_true(h))
    case V.JSpan{src, n} V.WObj{}:
      Empty.absurd(pq.goal(V.JSpan{src, n}, ind, close, V.WObj{}, tail), M4.false_true(h))
    case V.JArr{V.JNull{}} V.WVal{}:
      Empty.absurd(pq.goal(V.JArr{V.JNull{}}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JArr{V.JBool{bl}} V.WVal{}:
      Empty.absurd(pq.goal(V.JArr{V.JBool{bl}}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JArr{V.JNum{raw}} V.WVal{}:
      Empty.absurd(pq.goal(V.JArr{V.JNum{raw}}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JArr{V.JStr{s}} V.WVal{}:
      Empty.absurd(pq.goal(V.JArr{V.JStr{s}}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JArr{V.JSpan{src, n}} V.WVal{}:
      Empty.absurd(pq.goal(V.JArr{V.JSpan{src, n}}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JArr{V.JArr{items}} V.WVal{}:
      Empty.absurd(pq.goal(V.JArr{V.JArr{items}}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JArr{V.JObj{pairs}} V.WVal{}:
      Empty.absurd(pq.goal(V.JArr{V.JObj{pairs}}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JArr{V.JNil{}} V.WVal{}:
      {==}
    case V.JArr{V.JCons{+hh, +tt}} V.WVal{}:
      +inner = "  " ++ ind
      Equal.cong(String, String, zz => SCon{'[', SCon{'\n', zz}}, (inner ++ (Print.pretty.go(V.JCons{hh, tt}, inner,
        "\n" ++ ind) ++ "]")) ++ tail,
        inner ++ pq.ct(V.JCons{hh, tt}, inner, "\n" ++ ind, SCon{']', tail}),
        pq.wrap(inner, Print.pretty.go(V.JCons{hh, tt}, inner, "\n" ++ ind), ']', tail, pq.ct(V.JCons{hh, tt}, inner,
          "\n" ++ ind, SCon{']', tail}),
          pq.tl(V.JCons{hh, tt}, inner, "\n" ++ ind, V.WArr{}, SCon{']', tail}, h)))
    case V.JArr{V.JPair{k, v, r}} V.WVal{}:
      Empty.absurd(pq.goal(V.JArr{V.JPair{k, v, r}}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JArr{V.JBind{src, n, v, r}} V.WVal{}:
      Empty.absurd(pq.goal(V.JArr{V.JBind{src, n, v, r}}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JArr{items} V.WArr{}:
      Empty.absurd(pq.goal(V.JArr{items}, ind, close, V.WArr{}, tail), M4.false_true(h))
    case V.JArr{items} V.WObj{}:
      Empty.absurd(pq.goal(V.JArr{items}, ind, close, V.WObj{}, tail), M4.false_true(h))
    case V.JObj{V.JNull{}} V.WVal{}:
      Empty.absurd(pq.goal(V.JObj{V.JNull{}}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JObj{V.JBool{bl}} V.WVal{}:
      Empty.absurd(pq.goal(V.JObj{V.JBool{bl}}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JObj{V.JNum{raw}} V.WVal{}:
      Empty.absurd(pq.goal(V.JObj{V.JNum{raw}}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JObj{V.JStr{s}} V.WVal{}:
      Empty.absurd(pq.goal(V.JObj{V.JStr{s}}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JObj{V.JSpan{src, n}} V.WVal{}:
      Empty.absurd(pq.goal(V.JObj{V.JSpan{src, n}}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JObj{V.JArr{items}} V.WVal{}:
      Empty.absurd(pq.goal(V.JObj{V.JArr{items}}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JObj{V.JObj{pairs}} V.WVal{}:
      Empty.absurd(pq.goal(V.JObj{V.JObj{pairs}}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JObj{V.JNil{}} V.WVal{}:
      {==}
    case V.JObj{V.JCons{hh, tt}} V.WVal{}:
      Empty.absurd(pq.goal(V.JObj{V.JCons{hh, tt}}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JObj{V.JPair{+k, +v, +r}} V.WVal{}:
      +inner = "  " ++ ind
      Equal.cong(String, String, zz => SCon{'{', SCon{'\n', zz}}, (inner ++ (Print.pretty.go(V.JPair{k, v, r}, inner,
        "\n" ++ ind) ++ "}")) ++ tail,
        inner ++ pq.ct(V.JPair{k, v, r}, inner, "\n" ++ ind, SCon{'}', tail}),
        pq.wrap(inner, Print.pretty.go(V.JPair{k, v, r}, inner, "\n" ++ ind), '}', tail, pq.ct(V.JPair{k, v, r}, inner,
          "\n" ++ ind, SCon{'}', tail}),
          pq.tl(V.JPair{k, v, r}, inner, "\n" ++ ind, V.WObj{}, SCon{'}', tail}, h)))
    case V.JObj{V.JBind{+src, +n, +v, +r}} V.WVal{}:
      +inner = "  " ++ ind
      Equal.cong(String, String, zz => SCon{'{', SCon{'\n', zz}}, (inner ++ (Print.pretty.go(V.JBind{src, n, v, r},
        inner, "\n" ++ ind) ++ "}")) ++ tail,
        inner ++ pq.ct(V.JBind{src, n, v, r}, inner, "\n" ++ ind, SCon{'}', tail}),
        pq.wrap(inner, Print.pretty.go(V.JBind{src, n, v, r}, inner, "\n" ++ ind), '}', tail, pq.ct(V.JBind{src, n, v,
          r}, inner, "\n" ++ ind, SCon{'}', tail}),
          pq.tl(V.JBind{src, n, v, r}, inner, "\n" ++ ind, V.WObj{}, SCon{'}', tail}, h)))
    case V.JObj{pairs} V.WArr{}:
      Empty.absurd(pq.goal(V.JObj{pairs}, ind, close, V.WArr{}, tail), M4.false_true(h))
    case V.JObj{pairs} V.WObj{}:
      Empty.absurd(pq.goal(V.JObj{pairs}, ind, close, V.WObj{}, tail), M4.false_true(h))
    case V.JNil{} V.WVal{}:
      Empty.absurd(pq.goal(V.JNil{}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JNil{} V.WArr{}:
      {==}
    case V.JNil{} V.WObj{}:
      {==}
    case V.JCons{hh, tt} V.WVal{}:
      Empty.absurd(pq.goal(V.JCons{hh, tt}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JCons{+hh, V.JNull{}} V.WArr{}:
      et = pq.right(V.wf.go(hh, V.WVal{}), V.wf.go(V.JNull{}, V.WArr{}), h)
      Empty.absurd(pq.goal(V.JCons{hh, V.JNull{}}, ind, close, V.WArr{}, tail), M4.false_true(et))
    case V.JCons{+hh, V.JBool{bl2}} V.WArr{}:
      et = pq.right(V.wf.go(hh, V.WVal{}), V.wf.go(V.JBool{bl2}, V.WArr{}), h)
      Empty.absurd(pq.goal(V.JCons{hh, V.JBool{bl2}}, ind, close, V.WArr{}, tail), M4.false_true(et))
    case V.JCons{+hh, V.JNum{raw2}} V.WArr{}:
      et = pq.right(V.wf.go(hh, V.WVal{}), V.wf.go(V.JNum{raw2}, V.WArr{}), h)
      Empty.absurd(pq.goal(V.JCons{hh, V.JNum{raw2}}, ind, close, V.WArr{}, tail), M4.false_true(et))
    case V.JCons{+hh, V.JStr{s2}} V.WArr{}:
      et = pq.right(V.wf.go(hh, V.WVal{}), V.wf.go(V.JStr{s2}, V.WArr{}), h)
      Empty.absurd(pq.goal(V.JCons{hh, V.JStr{s2}}, ind, close, V.WArr{}, tail), M4.false_true(et))
    case V.JCons{+hh, V.JSpan{src2, n2}} V.WArr{}:
      et = pq.right(V.wf.go(hh, V.WVal{}), V.wf.go(V.JSpan{src2, n2}, V.WArr{}), h)
      Empty.absurd(pq.goal(V.JCons{hh, V.JSpan{src2, n2}}, ind, close, V.WArr{}, tail), M4.false_true(et))
    case V.JCons{+hh, V.JArr{items2}} V.WArr{}:
      et = pq.right(V.wf.go(hh, V.WVal{}), V.wf.go(V.JArr{items2}, V.WArr{}), h)
      Empty.absurd(pq.goal(V.JCons{hh, V.JArr{items2}}, ind, close, V.WArr{}, tail), M4.false_true(et))
    case V.JCons{+hh, V.JObj{pairs2}} V.WArr{}:
      et = pq.right(V.wf.go(hh, V.WVal{}), V.wf.go(V.JObj{pairs2}, V.WArr{}), h)
      Empty.absurd(pq.goal(V.JCons{hh, V.JObj{pairs2}}, ind, close, V.WArr{}, tail), M4.false_true(et))
    case V.JCons{+hh, V.JNil{}} V.WArr{}:
      eh = pq.left(V.wf.go(hh, V.WVal{}), V.wf.go(V.JNil{}, V.WArr{}), h)
      pq.last(Print.pretty.go(hh, ind, ""), close, tail, M3.gt(pq.g(hh, ind, ""), close ++ tail),
        pq.tl(hh, ind, "", V.WVal{}, close ++ tail, eh))
    case V.JCons{+hh, V.JCons{+h2, +t2}} V.WArr{}:
      eh = pq.left(V.wf.go(hh, V.WVal{}), V.wf.go(V.JCons{h2, t2}, V.WArr{}), h)
      et = pq.right(V.wf.go(hh, V.WVal{}), V.wf.go(V.JCons{h2, t2}, V.WArr{}), h)
      +cc = pq.ct(V.JCons{h2, t2}, ind, close, tail)
      pq.cell(Print.pretty.go(hh, ind, ""), "\n" ++ ind, Print.pretty.go(V.JCons{h2, t2}, ind, close), tail, cc,
        M3.gt(pq.g(hh, ind, ""), SCon{',', "\n" ++ ind ++ cc}), pq.tl(V.JCons{h2, t2}, ind, close, V.WArr{}, tail, et),
        pq.tl(hh, ind, "", V.WVal{}, SCon{',', "\n" ++ ind ++ cc}, eh))
    case V.JCons{+hh, V.JPair{k2, v2, r2}} V.WArr{}:
      et = pq.right(V.wf.go(hh, V.WVal{}), V.wf.go(V.JPair{k2, v2, r2}, V.WArr{}), h)
      Empty.absurd(pq.goal(V.JCons{hh, V.JPair{k2, v2, r2}}, ind, close, V.WArr{}, tail), M4.false_true(et))
    case V.JCons{+hh, V.JBind{src2, n2, v2, r2}} V.WArr{}:
      et = pq.right(V.wf.go(hh, V.WVal{}), V.wf.go(V.JBind{src2, n2, v2, r2}, V.WArr{}), h)
      Empty.absurd(pq.goal(V.JCons{hh, V.JBind{src2, n2, v2, r2}}, ind, close, V.WArr{}, tail), M4.false_true(et))
    case V.JCons{hh, tt} V.WObj{}:
      Empty.absurd(pq.goal(V.JCons{hh, tt}, ind, close, V.WObj{}, tail), M4.false_true(h))
    case V.JPair{k, v, r} V.WVal{}:
      Empty.absurd(pq.goal(V.JPair{k, v, r}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JPair{k, v, r} V.WArr{}:
      Empty.absurd(pq.goal(V.JPair{k, v, r}, ind, close, V.WArr{}, tail), M4.false_true(h))
    case V.JPair{+k, +v, V.JNull{}} V.WObj{}:
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      Empty.absurd(pq.goal(V.JPair{k, v, V.JNull{}}, ind, close, V.WObj{}, tail), M4.false_true(er))
    case V.JPair{+k, +v, V.JBool{bl2}} V.WObj{}:
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JBool{bl2}, V.WObj{}), h)
      Empty.absurd(pq.goal(V.JPair{k, v, V.JBool{bl2}}, ind, close, V.WObj{}, tail), M4.false_true(er))
    case V.JPair{+k, +v, V.JNum{raw2}} V.WObj{}:
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JNum{raw2}, V.WObj{}), h)
      Empty.absurd(pq.goal(V.JPair{k, v, V.JNum{raw2}}, ind, close, V.WObj{}, tail), M4.false_true(er))
    case V.JPair{+k, +v, V.JStr{s2}} V.WObj{}:
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JStr{s2}, V.WObj{}), h)
      Empty.absurd(pq.goal(V.JPair{k, v, V.JStr{s2}}, ind, close, V.WObj{}, tail), M4.false_true(er))
    case V.JPair{+k, +v, V.JSpan{src2, n2}} V.WObj{}:
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JSpan{src2, n2}, V.WObj{}), h)
      Empty.absurd(pq.goal(V.JPair{k, v, V.JSpan{src2, n2}}, ind, close, V.WObj{}, tail), M4.false_true(er))
    case V.JPair{+k, +v, V.JArr{items2}} V.WObj{}:
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JArr{items2}, V.WObj{}), h)
      Empty.absurd(pq.goal(V.JPair{k, v, V.JArr{items2}}, ind, close, V.WObj{}, tail), M4.false_true(er))
    case V.JPair{+k, +v, V.JObj{pairs2}} V.WObj{}:
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JObj{pairs2}, V.WObj{}), h)
      Empty.absurd(pq.goal(V.JPair{k, v, V.JObj{pairs2}}, ind, close, V.WObj{}, tail), M4.false_true(er))
    case V.JPair{+k, +v, V.JNil{}} V.WObj{}:
      ev = pq.left(V.wf.go(v, V.WVal{}), V.wf.go(V.JNil{}, V.WObj{}), h)
      +gv = M3.gt(pq.g(v, ind, ""), close ++ tail)
      pq.mem(k, ": " ++ (Print.pretty.go(v, ind, "") ++ close), tail, SCon{':', SCon{' ', gv}},
        Equal.cong(String, String, zz => SCon{':', SCon{' ', zz}}, (Print.pretty.go(v, ind, "") ++ close) ++ tail,
          gv, pq.last(Print.pretty.go(v, ind, ""), close, tail, gv, pq.tl(v, ind, "", V.WVal{}, close ++ tail, ev))))
    case V.JPair{+k, +v, V.JCons{hh2, tt2}} V.WObj{}:
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JCons{hh2, tt2}, V.WObj{}), h)
      Empty.absurd(pq.goal(V.JPair{k, v, V.JCons{hh2, tt2}}, ind, close, V.WObj{}, tail), M4.false_true(er))
    case V.JPair{+k, +v, V.JPair{+k2, +v2, +r2}} V.WObj{}:
      ev = pq.left(V.wf.go(v, V.WVal{}), V.wf.go(V.JPair{k2, v2, r2}, V.WObj{}), h)
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JPair{k2, v2, r2}, V.WObj{}), h)
      +cc = pq.ct(V.JPair{k2, v2, r2}, ind, close, tail)
      +gv = M3.gt(pq.g(v, ind, ""), SCon{',', "\n" ++ ind ++ cc})
      +rest = Print.pretty.go(v, ind, "") ++ (",\n" ++ ind ++ Print.pretty.go(V.JPair{k2, v2, r2}, ind, close))
      pq.mem(k, ": " ++ rest, tail, SCon{':', SCon{' ', gv}},
        Equal.cong(String, String, zz => SCon{':', SCon{' ', zz}}, rest ++ tail, gv,
          pq.cell(Print.pretty.go(v, ind, ""), "\n" ++ ind, Print.pretty.go(V.JPair{k2, v2, r2}, ind, close), tail, cc,
            gv,
            pq.tl(V.JPair{k2, v2, r2}, ind, close, V.WObj{}, tail, er), pq.tl(v, ind, "", V.WVal{}, SCon{',',
              "\n" ++ ind ++ cc}, ev))))
    case V.JPair{+k, +v, V.JBind{+src2, +n2, +v2, +r2}} V.WObj{}:
      ev = pq.left(V.wf.go(v, V.WVal{}), V.wf.go(V.JBind{src2, n2, v2, r2}, V.WObj{}), h)
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JBind{src2, n2, v2, r2}, V.WObj{}), h)
      +cc = pq.ct(V.JBind{src2, n2, v2, r2}, ind, close, tail)
      +gv = M3.gt(pq.g(v, ind, ""), SCon{',', "\n" ++ ind ++ cc})
      +rest = Print.pretty.go(v, ind, "") ++ (",\n" ++ ind ++ Print.pretty.go(V.JBind{src2, n2, v2, r2}, ind, close))
      pq.mem(k, ": " ++ rest, tail, SCon{':', SCon{' ', gv}},
        Equal.cong(String, String, zz => SCon{':', SCon{' ', zz}}, rest ++ tail, gv,
          pq.cell(Print.pretty.go(v, ind, ""), "\n" ++ ind, Print.pretty.go(V.JBind{src2, n2, v2, r2}, ind, close),
            tail, cc, gv,
            pq.tl(V.JBind{src2, n2, v2, r2}, ind, close, V.WObj{}, tail, er), pq.tl(v, ind, "", V.WVal{}, SCon{',',
              "\n" ++ ind ++ cc}, ev))))
    case V.JBind{src, n, v, r} V.WVal{}:
      Empty.absurd(pq.goal(V.JBind{src, n, v, r}, ind, close, V.WVal{}, tail), M4.false_true(h))
    case V.JBind{src, n, v, r} V.WArr{}:
      Empty.absurd(pq.goal(V.JBind{src, n, v, r}, ind, close, V.WArr{}, tail), M4.false_true(h))
    case V.JBind{+src, +n, +v, V.JNull{}} V.WObj{}:
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      Empty.absurd(pq.goal(V.JBind{src, n, v, V.JNull{}}, ind, close, V.WObj{}, tail), M4.false_true(er))
    case V.JBind{+src, +n, +v, V.JBool{bl2}} V.WObj{}:
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JBool{bl2}, V.WObj{}), h)
      Empty.absurd(pq.goal(V.JBind{src, n, v, V.JBool{bl2}}, ind, close, V.WObj{}, tail), M4.false_true(er))
    case V.JBind{+src, +n, +v, V.JNum{raw2}} V.WObj{}:
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JNum{raw2}, V.WObj{}), h)
      Empty.absurd(pq.goal(V.JBind{src, n, v, V.JNum{raw2}}, ind, close, V.WObj{}, tail), M4.false_true(er))
    case V.JBind{+src, +n, +v, V.JStr{s2}} V.WObj{}:
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JStr{s2}, V.WObj{}), h)
      Empty.absurd(pq.goal(V.JBind{src, n, v, V.JStr{s2}}, ind, close, V.WObj{}, tail), M4.false_true(er))
    case V.JBind{+src, +n, +v, V.JSpan{src2, n2}} V.WObj{}:
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JSpan{src2, n2}, V.WObj{}), h)
      Empty.absurd(pq.goal(V.JBind{src, n, v, V.JSpan{src2, n2}}, ind, close, V.WObj{}, tail), M4.false_true(er))
    case V.JBind{+src, +n, +v, V.JArr{items2}} V.WObj{}:
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JArr{items2}, V.WObj{}), h)
      Empty.absurd(pq.goal(V.JBind{src, n, v, V.JArr{items2}}, ind, close, V.WObj{}, tail), M4.false_true(er))
    case V.JBind{+src, +n, +v, V.JObj{pairs2}} V.WObj{}:
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JObj{pairs2}, V.WObj{}), h)
      Empty.absurd(pq.goal(V.JBind{src, n, v, V.JObj{pairs2}}, ind, close, V.WObj{}, tail), M4.false_true(er))
    case V.JBind{+src, +n, +v, V.JNil{}} V.WObj{}:
      ev = pq.left(V.wf.go(v, V.WVal{}), V.wf.go(V.JNil{}, V.WObj{}), h)
      +gv = M3.gt(pq.g(v, ind, ""), close ++ tail)
      pq.mem(V.span.str(src, n, U32.is_zero(n)), ": " ++ (Print.pretty.go(v, ind, "") ++ close), tail, SCon{':',
        SCon{' ', gv}},
        Equal.cong(String, String, zz => SCon{':', SCon{' ', zz}}, (Print.pretty.go(v, ind, "") ++ close) ++ tail,
          gv, pq.last(Print.pretty.go(v, ind, ""), close, tail, gv, pq.tl(v, ind, "", V.WVal{}, close ++ tail, ev))))
    case V.JBind{+src, +n, +v, V.JCons{hh2, tt2}} V.WObj{}:
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JCons{hh2, tt2}, V.WObj{}), h)
      Empty.absurd(pq.goal(V.JBind{src, n, v, V.JCons{hh2, tt2}}, ind, close, V.WObj{}, tail), M4.false_true(er))
    case V.JBind{+src, +n, +v, V.JPair{+k2, +v2, +r2}} V.WObj{}:
      ev = pq.left(V.wf.go(v, V.WVal{}), V.wf.go(V.JPair{k2, v2, r2}, V.WObj{}), h)
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JPair{k2, v2, r2}, V.WObj{}), h)
      +cc = pq.ct(V.JPair{k2, v2, r2}, ind, close, tail)
      +gv = M3.gt(pq.g(v, ind, ""), SCon{',', "\n" ++ ind ++ cc})
      +rest = Print.pretty.go(v, ind, "") ++ (",\n" ++ ind ++ Print.pretty.go(V.JPair{k2, v2, r2}, ind, close))
      pq.mem(V.span.str(src, n, U32.is_zero(n)), ": " ++ rest, tail, SCon{':', SCon{' ', gv}},
        Equal.cong(String, String, zz => SCon{':', SCon{' ', zz}}, rest ++ tail, gv,
          pq.cell(Print.pretty.go(v, ind, ""), "\n" ++ ind, Print.pretty.go(V.JPair{k2, v2, r2}, ind, close), tail, cc,
            gv,
            pq.tl(V.JPair{k2, v2, r2}, ind, close, V.WObj{}, tail, er), pq.tl(v, ind, "", V.WVal{}, SCon{',',
              "\n" ++ ind ++ cc}, ev))))
    case V.JBind{+src, +n, +v, V.JBind{+src2, +n2, +v2, +r2}} V.WObj{}:
      ev = pq.left(V.wf.go(v, V.WVal{}), V.wf.go(V.JBind{src2, n2, v2, r2}, V.WObj{}), h)
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(V.JBind{src2, n2, v2, r2}, V.WObj{}), h)
      +cc = pq.ct(V.JBind{src2, n2, v2, r2}, ind, close, tail)
      +gv = M3.gt(pq.g(v, ind, ""), SCon{',', "\n" ++ ind ++ cc})
      +rest = Print.pretty.go(v, ind, "") ++ (",\n" ++ ind ++ Print.pretty.go(V.JBind{src2, n2, v2, r2}, ind, close))
      pq.mem(V.span.str(src, n, U32.is_zero(n)), ": " ++ rest, tail, SCon{':', SCon{' ', gv}},
        Equal.cong(String, String, zz => SCon{':', SCon{' ', zz}}, rest ++ tail, gv,
          pq.cell(Print.pretty.go(v, ind, ""), "\n" ++ ind, Print.pretty.go(V.JBind{src2, n2, v2, r2}, ind, close),
            tail, cc, gv,
            pq.tl(V.JBind{src2, n2, v2, r2}, ind, close, V.WObj{}, tail, er), pq.tl(v, ind, "", V.WVal{}, SCon{',',
              "\n" ++ ind ++ cc}, ev))))

# Third, the derivation follows the rules, and stands for the value print
# would give back

# both sides of an and hold
law pq.and2:
  for aa: Bool
  for bb: Bool
  for ea: {aa == True{} : Bool}
  for eb: {bb == True{} : Bool}
  {Bool.and(aa, bb) == True{} : Bool}

def pq.and2(aa, bb, ea, eb):
  sa = Equal.sym(Bool, aa, True{}, ea)
  sb = Equal.sym(Bool, bb, True{}, eb)
  %sa : {Bool.and(_, bb) == True{} : Bool}
  %sb : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# where a derivation of a value or a chain stands
def pq.gk(sh: V.Shape) -> D2.GK:
  match sh:
    case V.WVal{}:
      D2.GKVal{}
    case V.WArr{}:
      D2.GKArr{}
    case V.WObj{}:
      D2.GKObj{}

# a number's word follows the rules
law pq.num_ok:
  for +raw: String
  for both: ({Bool.pick(V.Json, String.eq(raw, "null"), V.JNull{}, Bool.pick(V.Json, String.eq(raw, "true"),
    V.JBool{True{}}, Bool.pick(V.Json, String.eq(raw, "false"), V.JBool{False{}}, V.JNum{raw}))) == V.JNum{raw}
    : V.Json} & {Bool.or(String.eq(raw, "null"), Bool.or(String.eq(raw, "true"), Bool.or(String.eq(raw, "false"),
    V.num.ok(raw)))) == True{} : Bool})
  {D1.lit_or_num(raw) == True{} : Bool}

def pq.num_ok(raw, both):
  (_ew, eo) = both
  eg = L1.num_grammar(raw)
  %eg : {Bool.or(String.eq(raw, "null"), Bool.or(String.eq(raw, "true"), Bool.or(String.eq(raw, "false"), _)))
    == True{} : Bool}
  eo

# a number's word stands for the number
law pq.num_val:
  for +raw: String
  for both: ({Bool.pick(V.Json, String.eq(raw, "null"), V.JNull{}, Bool.pick(V.Json, String.eq(raw, "true"),
    V.JBool{True{}}, Bool.pick(V.Json, String.eq(raw, "false"), V.JBool{False{}}, V.JNum{raw}))) == V.JNum{raw}
    : V.Json} & {Bool.or(String.eq(raw, "null"), Bool.or(String.eq(raw, "true"), Bool.or(String.eq(raw, "false"),
    V.num.ok(raw)))) == True{} : Bool})
  {L2.g.word(raw) == V.JNum{raw} : V.Json}

def pq.num_val(_raw, both):
  (ew, _eo) = both
  ew

# two cells, equal field by field
law pq.cons2:
  for +aa: V.Json
  for +a2: V.Json
  for +bb: V.Json
  for +b2: V.Json
  for ea: {aa == a2 : V.Json}
  for eb: {bb == b2 : V.Json}
  {V.JCons{aa, bb} == V.JCons{a2, b2} : V.Json}

def pq.cons2(aa, a2, bb, b2, ea, eb):
  Equal.trans(V.Json, V.JCons{aa, bb}, V.JCons{a2, bb}, V.JCons{a2, b2},
    Equal.cong(V.Json, V.Json, zz => V.JCons{zz, bb}, aa, a2, ea),
    Equal.cong(V.Json, V.Json, zz => V.JCons{a2, zz}, bb, b2, eb))

# two members, equal field by field
law pq.pair3:
  for +kk: String
  for +k2: String
  for +aa: V.Json
  for +a2: V.Json
  for +bb: V.Json
  for +b2: V.Json
  for ek: {kk == k2 : String}
  for ea: {aa == a2 : V.Json}
  for eb: {bb == b2 : V.Json}
  {V.JPair{kk, aa, bb} == V.JPair{k2, a2, b2} : V.Json}

def pq.pair3(kk, k2, aa, a2, bb, b2, ek, ea, eb):
  Equal.trans(V.Json, V.JPair{kk, aa, bb}, V.JPair{k2, aa, bb}, V.JPair{k2, a2, b2},
    Equal.cong(String, V.Json, zz => V.JPair{zz, aa, bb}, kk, k2, ek),
    Equal.trans(V.Json, V.JPair{k2, aa, bb}, V.JPair{k2, a2, bb}, V.JPair{k2, a2, b2},
      Equal.cong(V.Json, V.Json, zz => V.JPair{k2, zz, bb}, aa, a2, ea),
      Equal.cong(V.Json, V.Json, zz => V.JPair{k2, a2, zz}, bb, b2, eb)))

# the whitespace after an element or member is whitespace
law pq.ww:
  for +tl: V.Json
  for +close: String
  for hc: {D1.all_ws(close) == True{} : Bool}
  {D1.all_ws(pq.w(tl, close)) == True{} : Bool}

def pq.ww(tl, _close, hc):
  match tl:
    case V.JNull{}:
      {==}
    case V.JBool{_bl}:
      {==}
    case V.JNum{_raw}:
      {==}
    case V.JStr{_s}:
      {==}
    case V.JSpan{_src, _n}:
      {==}
    case V.JArr{_items}:
      {==}
    case V.JObj{_pairs}:
      {==}
    case V.JNil{}:
      hc
    case V.JCons{_hh, _tt}:
      {==}
    case V.JPair{_k, _v, _r}:
      {==}
    case V.JBind{_src, _n, _v, _r}:
      {==}

# the derivation of a well-formed value or chain follows the rules where it
# stands, when `ind` and `close` are whitespace
law pq.ok:
  for +val: V.Json
  for +ind: String
  for +close: String
  for sh: V.Shape
  for +h: {V.wf.go(val, sh) == True{} : Bool}
  for +hi: {D1.all_ws(ind) == True{} : Bool}
  for +hc: {D1.all_ws(close) == True{} : Bool}
  {D2.g.ok(pq.g(val, ind, close), pq.gk(sh)) == True{} : Bool}

def pq.ok(val, ind, close, sh, h, hi, hc):
  match val sh:
    case V.JNull{} V.WVal{}:
      {==}
    case V.JNull{} V.WArr{}:
      Empty.absurd({D2.g.ok(pq.g(V.JNull{}, ind, close), pq.gk(V.WArr{})) == True{} : Bool}, M4.false_true(h))
    case V.JNull{} V.WObj{}:
      Empty.absurd({D2.g.ok(pq.g(V.JNull{}, ind, close), pq.gk(V.WObj{})) == True{} : Bool}, M4.false_true(h))
    case V.JBool{True{}} V.WVal{}:
      {==}
    case V.JBool{False{}} V.WVal{}:
      {==}
    case V.JBool{bl} V.WArr{}:
      Empty.absurd({D2.g.ok(pq.g(V.JBool{bl}, ind, close), pq.gk(V.WArr{})) == True{} : Bool}, M4.false_true(h))
    case V.JBool{bl} V.WObj{}:
      Empty.absurd({D2.g.ok(pq.g(V.JBool{bl}, ind, close), pq.gk(V.WObj{})) == True{} : Bool}, M4.false_true(h))
    case V.JNum{+raw} V.WVal{}:
      pq.num_ok(raw, M6.word_num.at(String.eq(raw, "null"), String.eq(raw, "true"), String.eq(raw, "false"), raw, {==},
        {==},
        {==}, h))
    case V.JNum{raw} V.WArr{}:
      Empty.absurd({D2.g.ok(pq.g(V.JNum{raw}, ind, close), pq.gk(V.WArr{})) == True{} : Bool}, M4.false_true(h))
    case V.JNum{raw} V.WObj{}:
      Empty.absurd({D2.g.ok(pq.g(V.JNum{raw}, ind, close), pq.gk(V.WObj{})) == True{} : Bool}, M4.false_true(h))
    case V.JStr{s} V.WVal{}:
      pq.pcs_ok(s)
    case V.JStr{s} V.WArr{}:
      Empty.absurd({D2.g.ok(pq.g(V.JStr{s}, ind, close), pq.gk(V.WArr{})) == True{} : Bool}, M4.false_true(h))
    case V.JStr{s} V.WObj{}:
      Empty.absurd({D2.g.ok(pq.g(V.JStr{s}, ind, close), pq.gk(V.WObj{})) == True{} : Bool}, M4.false_true(h))
    case V.JSpan{src, +n} V.WVal{}:
      pq.pcs_ok(V.span.str(src, n, U32.is_zero(n)))
    case V.JSpan{src, n} V.WArr{}:
      Empty.absurd({D2.g.ok(pq.g(V.JSpan{src, n}, ind, close), pq.gk(V.WArr{})) == True{} : Bool}, M4.false_true(h))
    case V.JSpan{src, n} V.WObj{}:
      Empty.absurd({D2.g.ok(pq.g(V.JSpan{src, n}, ind, close), pq.gk(V.WObj{})) == True{} : Bool}, M4.false_true(h))
    case V.JArr{V.JNull{}} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JArr{V.JNull{}}, ind, close), pq.gk(V.WVal{})) == True{} : Bool}, M4.false_true(h))
    case V.JArr{V.JBool{bl}} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JArr{V.JBool{bl}}, ind, close), pq.gk(V.WVal{})) == True{} : Bool}, M4.false_true(h))
    case V.JArr{V.JNum{raw}} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JArr{V.JNum{raw}}, ind, close), pq.gk(V.WVal{})) == True{} : Bool}, M4.false_true(h))
    case V.JArr{V.JStr{s}} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JArr{V.JStr{s}}, ind, close), pq.gk(V.WVal{})) == True{} : Bool}, M4.false_true(h))
    case V.JArr{V.JSpan{src, n}} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JArr{V.JSpan{src, n}}, ind, close), pq.gk(V.WVal{})) == True{} : Bool},
        M4.false_true(h))
    case V.JArr{V.JArr{items}} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JArr{V.JArr{items}}, ind, close), pq.gk(V.WVal{})) == True{} : Bool},
        M4.false_true(h))
    case V.JArr{V.JObj{pairs}} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JArr{V.JObj{pairs}}, ind, close), pq.gk(V.WVal{})) == True{} : Bool},
        M4.false_true(h))
    case V.JArr{V.JNil{}} V.WVal{}:
      {==}
    case V.JArr{V.JCons{+hh, +tt}} V.WVal{}:
      +inner = "  " ++ ind
      eh = pq.left(V.wf.go(hh, V.WVal{}), V.wf.go(tt, V.WArr{}), h)
      et = pq.right(V.wf.go(hh, V.WVal{}), V.wf.go(tt, V.WArr{}), h)
      +gh = pq.g(hh, inner, "")
      +gr = pq.g(tt, inner, "\n" ++ ind)
      pq.and2(D1.all_ws("\n" ++ inner), Bool.and(D2.g.ok(gh, D2.GKVal{}), Bool.and(D1.all_ws(pq.w(tt,
        "\n" ++ ind)), D2.g.ok(gr, D2.GKArr{}))), hi, pq.and2(D2.g.ok(gh, D2.GKVal{}),
        Bool.and(D1.all_ws(pq.w(tt, "\n" ++ ind)), D2.g.ok(gr, D2.GKArr{})), pq.ok(hh, inner, "", V.WVal{}, eh,
          hi,
        {==}), pq.and2(D1.all_ws(pq.w(tt, "\n" ++ ind)), D2.g.ok(gr, D2.GKArr{}), pq.ww(tt, "\n" ++ ind, hi),
        pq.ok(tt, inner, "\n" ++ ind, V.WArr{}, et, hi, hi))))
    case V.JArr{V.JPair{k, v, r}} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JArr{V.JPair{k, v, r}}, ind, close), pq.gk(V.WVal{})) == True{} : Bool},
        M4.false_true(h))
    case V.JArr{V.JBind{src, n, v, r}} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JArr{V.JBind{src, n, v, r}}, ind, close), pq.gk(V.WVal{})) == True{} : Bool},
        M4.false_true(h))
    case V.JArr{items} V.WArr{}:
      Empty.absurd({D2.g.ok(pq.g(V.JArr{items}, ind, close), pq.gk(V.WArr{})) == True{} : Bool}, M4.false_true(h))
    case V.JArr{items} V.WObj{}:
      Empty.absurd({D2.g.ok(pq.g(V.JArr{items}, ind, close), pq.gk(V.WObj{})) == True{} : Bool}, M4.false_true(h))
    case V.JObj{V.JNull{}} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JObj{V.JNull{}}, ind, close), pq.gk(V.WVal{})) == True{} : Bool}, M4.false_true(h))
    case V.JObj{V.JBool{bl}} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JObj{V.JBool{bl}}, ind, close), pq.gk(V.WVal{})) == True{} : Bool}, M4.false_true(h))
    case V.JObj{V.JNum{raw}} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JObj{V.JNum{raw}}, ind, close), pq.gk(V.WVal{})) == True{} : Bool}, M4.false_true(h))
    case V.JObj{V.JStr{s}} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JObj{V.JStr{s}}, ind, close), pq.gk(V.WVal{})) == True{} : Bool}, M4.false_true(h))
    case V.JObj{V.JSpan{src, n}} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JObj{V.JSpan{src, n}}, ind, close), pq.gk(V.WVal{})) == True{} : Bool},
        M4.false_true(h))
    case V.JObj{V.JArr{items}} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JObj{V.JArr{items}}, ind, close), pq.gk(V.WVal{})) == True{} : Bool},
        M4.false_true(h))
    case V.JObj{V.JObj{pairs}} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JObj{V.JObj{pairs}}, ind, close), pq.gk(V.WVal{})) == True{} : Bool},
        M4.false_true(h))
    case V.JObj{V.JNil{}} V.WVal{}:
      {==}
    case V.JObj{V.JCons{hh, tt}} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JObj{V.JCons{hh, tt}}, ind, close), pq.gk(V.WVal{})) == True{} : Bool},
        M4.false_true(h))
    case V.JObj{V.JPair{k, +v, +r}} V.WVal{}:
      +inner = "  " ++ ind
      ev = pq.left(V.wf.go(v, V.WVal{}), V.wf.go(r, V.WObj{}), h)
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(r, V.WObj{}), h)
      +gv = pq.g(v, inner, "")
      +gr = pq.g(r, inner, "\n" ++ ind)
      +ps = pq.pcs(k)
      pq.and2(D1.all_ws("\n" ++ inner), Bool.and(D2.spell_ok(ps), Bool.and(D1.all_ws(""),
        Bool.and(D1.all_ws(" "), Bool.and(D2.g.ok(gv, D2.GKVal{}), Bool.and(D1.all_ws(pq.w(r, "\n" ++ ind)),
        D2.g.ok(gr, D2.GKObj{})))))), hi,
        pq.and2(D2.spell_ok(ps), Bool.and(D1.all_ws(""), Bool.and(D1.all_ws(" "), Bool.and(D2.g.ok(gv,
          D2.GKVal{}), Bool.and(D1.all_ws(pq.w(r, "\n" ++ ind)), D2.g.ok(gr, D2.GKObj{}))))), pq.pcs_ok(k),
        pq.and2(D1.all_ws(""), Bool.and(D1.all_ws(" "), Bool.and(D2.g.ok(gv, D2.GKVal{}),
          Bool.and(D1.all_ws(pq.w(r, "\n" ++ ind)), D2.g.ok(gr, D2.GKObj{})))), {==}, pq.and2(D1.all_ws(" "),
          Bool.and(D2.g.ok(gv, D2.GKVal{}), Bool.and(D1.all_ws(pq.w(r, "\n" ++ ind)), D2.g.ok(gr,
          D2.GKObj{}))), {==},
        pq.and2(D2.g.ok(gv, D2.GKVal{}), Bool.and(D1.all_ws(pq.w(r, "\n" ++ ind)), D2.g.ok(gr, D2.GKObj{})),
          pq.ok(v, inner, "", V.WVal{}, ev, hi, {==}),
        pq.and2(D1.all_ws(pq.w(r, "\n" ++ ind)), D2.g.ok(gr, D2.GKObj{}), pq.ww(r, "\n" ++ ind, hi),
        pq.ok(r, inner, "\n" ++ ind, V.WObj{}, er, hi, hi)))))))
    case V.JObj{V.JBind{src, +n, +v, +r}} V.WVal{}:
      +inner = "  " ++ ind
      ev = pq.left(V.wf.go(v, V.WVal{}), V.wf.go(r, V.WObj{}), h)
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(r, V.WObj{}), h)
      +gv = pq.g(v, inner, "")
      +gr = pq.g(r, inner, "\n" ++ ind)
      +ps = pq.pcs(V.span.str(src, n, U32.is_zero(n)))
      pq.and2(D1.all_ws("\n" ++ inner), Bool.and(D2.spell_ok(ps), Bool.and(D1.all_ws(""),
        Bool.and(D1.all_ws(" "), Bool.and(D2.g.ok(gv, D2.GKVal{}), Bool.and(D1.all_ws(pq.w(r, "\n" ++ ind)),
        D2.g.ok(gr, D2.GKObj{})))))), hi,
        pq.and2(D2.spell_ok(ps), Bool.and(D1.all_ws(""), Bool.and(D1.all_ws(" "), Bool.and(D2.g.ok(gv,
          D2.GKVal{}), Bool.and(D1.all_ws(pq.w(r, "\n" ++ ind)), D2.g.ok(gr, D2.GKObj{}))))),
          pq.pcs_ok(V.span.str(src, n, U32.is_zero(n))),
        pq.and2(D1.all_ws(""), Bool.and(D1.all_ws(" "), Bool.and(D2.g.ok(gv, D2.GKVal{}),
          Bool.and(D1.all_ws(pq.w(r, "\n" ++ ind)), D2.g.ok(gr, D2.GKObj{})))), {==}, pq.and2(D1.all_ws(" "),
          Bool.and(D2.g.ok(gv, D2.GKVal{}), Bool.and(D1.all_ws(pq.w(r, "\n" ++ ind)), D2.g.ok(gr,
          D2.GKObj{}))), {==},
        pq.and2(D2.g.ok(gv, D2.GKVal{}), Bool.and(D1.all_ws(pq.w(r, "\n" ++ ind)), D2.g.ok(gr, D2.GKObj{})),
          pq.ok(v, inner, "", V.WVal{}, ev, hi, {==}),
        pq.and2(D1.all_ws(pq.w(r, "\n" ++ ind)), D2.g.ok(gr, D2.GKObj{}), pq.ww(r, "\n" ++ ind, hi),
        pq.ok(r, inner, "\n" ++ ind, V.WObj{}, er, hi, hi)))))))
    case V.JObj{pairs} V.WArr{}:
      Empty.absurd({D2.g.ok(pq.g(V.JObj{pairs}, ind, close), pq.gk(V.WArr{})) == True{} : Bool}, M4.false_true(h))
    case V.JObj{pairs} V.WObj{}:
      Empty.absurd({D2.g.ok(pq.g(V.JObj{pairs}, ind, close), pq.gk(V.WObj{})) == True{} : Bool}, M4.false_true(h))
    case V.JNil{} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JNil{}, ind, close), pq.gk(V.WVal{})) == True{} : Bool}, M4.false_true(h))
    case V.JNil{} V.WArr{}:
      {==}
    case V.JNil{} V.WObj{}:
      {==}
    case V.JCons{hh, tt} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JCons{hh, tt}, ind, close), pq.gk(V.WVal{})) == True{} : Bool}, M4.false_true(h))
    case V.JCons{+hh, +tt} V.WArr{}:
      eh = pq.left(V.wf.go(hh, V.WVal{}), V.wf.go(tt, V.WArr{}), h)
      et = pq.right(V.wf.go(hh, V.WVal{}), V.wf.go(tt, V.WArr{}), h)
      +gh = pq.g(hh, ind, "")
      +gr = pq.g(tt, ind, close)
      pq.and2(D1.all_ws("\n" ++ ind), Bool.and(D2.g.ok(gh, D2.GKVal{}), Bool.and(D1.all_ws(pq.w(tt, close)),
        D2.g.ok(gr, D2.GKArr{}))), hi, pq.and2(D2.g.ok(gh, D2.GKVal{}), Bool.and(D1.all_ws(pq.w(tt, close)),
        D2.g.ok(gr, D2.GKArr{})), pq.ok(hh, ind, "", V.WVal{}, eh, hi, {==}), pq.and2(D1.all_ws(pq.w(tt, close)),
        D2.g.ok(gr, D2.GKArr{}), pq.ww(tt, close, hc), pq.ok(tt, ind, close, V.WArr{}, et, hi, hc))))
    case V.JCons{hh, tt} V.WObj{}:
      Empty.absurd({D2.g.ok(pq.g(V.JCons{hh, tt}, ind, close), pq.gk(V.WObj{})) == True{} : Bool}, M4.false_true(h))
    case V.JPair{k, v, r} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JPair{k, v, r}, ind, close), pq.gk(V.WVal{})) == True{} : Bool}, M4.false_true(h))
    case V.JPair{k, v, r} V.WArr{}:
      Empty.absurd({D2.g.ok(pq.g(V.JPair{k, v, r}, ind, close), pq.gk(V.WArr{})) == True{} : Bool}, M4.false_true(h))
    case V.JPair{k, +v, +r} V.WObj{}:
      ev = pq.left(V.wf.go(v, V.WVal{}), V.wf.go(r, V.WObj{}), h)
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(r, V.WObj{}), h)
      +gv = pq.g(v, ind, "")
      +gr = pq.g(r, ind, close)
      +ps = pq.pcs(k)
      pq.and2(D1.all_ws("\n" ++ ind), Bool.and(D2.spell_ok(ps), Bool.and(D1.all_ws(""),
        Bool.and(D1.all_ws(" "), Bool.and(D2.g.ok(gv, D2.GKVal{}), Bool.and(D1.all_ws(pq.w(r, close)),
        D2.g.ok(gr, D2.GKObj{})))))), hi,
        pq.and2(D2.spell_ok(ps), Bool.and(D1.all_ws(""), Bool.and(D1.all_ws(" "), Bool.and(D2.g.ok(gv,
          D2.GKVal{}), Bool.and(D1.all_ws(pq.w(r, close)), D2.g.ok(gr, D2.GKObj{}))))), pq.pcs_ok(k),
        pq.and2(D1.all_ws(""), Bool.and(D1.all_ws(" "), Bool.and(D2.g.ok(gv, D2.GKVal{}),
          Bool.and(D1.all_ws(pq.w(r, close)), D2.g.ok(gr, D2.GKObj{})))), {==}, pq.and2(D1.all_ws(" "),
          Bool.and(D2.g.ok(gv, D2.GKVal{}), Bool.and(D1.all_ws(pq.w(r, close)), D2.g.ok(gr, D2.GKObj{}))),
          {==},
        pq.and2(D2.g.ok(gv, D2.GKVal{}), Bool.and(D1.all_ws(pq.w(r, close)), D2.g.ok(gr, D2.GKObj{})),
          pq.ok(v, ind, "", V.WVal{}, ev, hi, {==}),
        pq.and2(D1.all_ws(pq.w(r, close)), D2.g.ok(gr, D2.GKObj{}), pq.ww(r, close, hc),
        pq.ok(r, ind, close, V.WObj{}, er, hi, hc)))))))
    case V.JBind{src, n, v, r} V.WVal{}:
      Empty.absurd({D2.g.ok(pq.g(V.JBind{src, n, v, r}, ind, close), pq.gk(V.WVal{})) == True{} : Bool},
        M4.false_true(h))
    case V.JBind{src, n, v, r} V.WArr{}:
      Empty.absurd({D2.g.ok(pq.g(V.JBind{src, n, v, r}, ind, close), pq.gk(V.WArr{})) == True{} : Bool},
        M4.false_true(h))
    case V.JBind{src, +n, +v, +r} V.WObj{}:
      ev = pq.left(V.wf.go(v, V.WVal{}), V.wf.go(r, V.WObj{}), h)
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(r, V.WObj{}), h)
      +gv = pq.g(v, ind, "")
      +gr = pq.g(r, ind, close)
      +ps = pq.pcs(V.span.str(src, n, U32.is_zero(n)))
      pq.and2(D1.all_ws("\n" ++ ind), Bool.and(D2.spell_ok(ps), Bool.and(D1.all_ws(""),
        Bool.and(D1.all_ws(" "), Bool.and(D2.g.ok(gv, D2.GKVal{}), Bool.and(D1.all_ws(pq.w(r, close)),
        D2.g.ok(gr, D2.GKObj{})))))), hi,
        pq.and2(D2.spell_ok(ps), Bool.and(D1.all_ws(""), Bool.and(D1.all_ws(" "), Bool.and(D2.g.ok(gv,
          D2.GKVal{}), Bool.and(D1.all_ws(pq.w(r, close)), D2.g.ok(gr, D2.GKObj{}))))),
          pq.pcs_ok(V.span.str(src, n, U32.is_zero(n))),
        pq.and2(D1.all_ws(""), Bool.and(D1.all_ws(" "), Bool.and(D2.g.ok(gv, D2.GKVal{}),
          Bool.and(D1.all_ws(pq.w(r, close)), D2.g.ok(gr, D2.GKObj{})))), {==}, pq.and2(D1.all_ws(" "),
          Bool.and(D2.g.ok(gv, D2.GKVal{}), Bool.and(D1.all_ws(pq.w(r, close)), D2.g.ok(gr, D2.GKObj{}))),
          {==},
        pq.and2(D2.g.ok(gv, D2.GKVal{}), Bool.and(D1.all_ws(pq.w(r, close)), D2.g.ok(gr, D2.GKObj{})),
          pq.ok(v, ind, "", V.WVal{}, ev, hi, {==}),
        pq.and2(D1.all_ws(pq.w(r, close)), D2.g.ok(gr, D2.GKObj{}), pq.ww(r, close, hc),
        pq.ok(r, ind, close, V.WObj{}, er, hi, hc)))))))

# the derivation of a well-formed value or chain stands for it as print
# writes it, owned
law pq.val:
  for +val: V.Json
  for +ind: String
  for +close: String
  for sh: V.Shape
  for +h: {V.wf.go(val, sh) == True{} : Bool}
  {L2.g.val(pq.g(val, ind, close)) == D1.fixv(D1.own(val)) : V.Json}

def pq.val(val, ind, close, sh, h):
  match val sh:
    case V.JNull{} V.WVal{}:
      {==}
    case V.JNull{} V.WArr{}:
      Empty.absurd({L2.g.val(pq.g(V.JNull{}, ind, close)) == D1.fixv(D1.own(V.JNull{})) : V.Json}, M4.false_true(h))
    case V.JNull{} V.WObj{}:
      Empty.absurd({L2.g.val(pq.g(V.JNull{}, ind, close)) == D1.fixv(D1.own(V.JNull{})) : V.Json}, M4.false_true(h))
    case V.JBool{True{}} V.WVal{}:
      {==}
    case V.JBool{False{}} V.WVal{}:
      {==}
    case V.JBool{bl} V.WArr{}:
      Empty.absurd({L2.g.val(pq.g(V.JBool{bl}, ind, close)) == D1.fixv(D1.own(V.JBool{bl})) : V.Json},
        M4.false_true(h))
    case V.JBool{bl} V.WObj{}:
      Empty.absurd({L2.g.val(pq.g(V.JBool{bl}, ind, close)) == D1.fixv(D1.own(V.JBool{bl})) : V.Json},
        M4.false_true(h))
    case V.JNum{+raw} V.WVal{}:
      pq.num_val(raw, M6.word_num.at(String.eq(raw, "null"), String.eq(raw, "true"), String.eq(raw, "false"), raw, {==},
        {==},
        {==}, h))
    case V.JNum{raw} V.WArr{}:
      Empty.absurd({L2.g.val(pq.g(V.JNum{raw}, ind, close)) == D1.fixv(D1.own(V.JNum{raw})) : V.Json},
        M4.false_true(h))
    case V.JNum{raw} V.WObj{}:
      Empty.absurd({L2.g.val(pq.g(V.JNum{raw}, ind, close)) == D1.fixv(D1.own(V.JNum{raw})) : V.Json},
        M4.false_true(h))
    case V.JStr{+s} V.WVal{}:
      Equal.cong(String, V.Json, zz => V.JStr{zz}, D2.spelled(pq.pcs(s)), D1.fix_str(s), pq.pcs_spelled(s))
    case V.JStr{s} V.WArr{}:
      Empty.absurd({L2.g.val(pq.g(V.JStr{s}, ind, close)) == D1.fixv(D1.own(V.JStr{s})) : V.Json}, M4.false_true(h))
    case V.JStr{s} V.WObj{}:
      Empty.absurd({L2.g.val(pq.g(V.JStr{s}, ind, close)) == D1.fixv(D1.own(V.JStr{s})) : V.Json}, M4.false_true(h))
    case V.JSpan{src, +n} V.WVal{}:
      +ss = V.span.str(src, n, U32.is_zero(n))
      Equal.cong(String, V.Json, zz => V.JStr{zz}, D2.spelled(pq.pcs(ss)), D1.fix_str(ss), pq.pcs_spelled(ss))
    case V.JSpan{src, n} V.WArr{}:
      Empty.absurd({L2.g.val(pq.g(V.JSpan{src, n}, ind, close)) == D1.fixv(D1.own(V.JSpan{src, n})) : V.Json},
        M4.false_true(h))
    case V.JSpan{src, n} V.WObj{}:
      Empty.absurd({L2.g.val(pq.g(V.JSpan{src, n}, ind, close)) == D1.fixv(D1.own(V.JSpan{src, n})) : V.Json},
        M4.false_true(h))
    case V.JArr{V.JNull{}} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JArr{V.JNull{}}, ind,
        close)) == D1.fixv(D1.own(V.JArr{V.JNull{}})) : V.Json}, M4.false_true(h))
    case V.JArr{V.JBool{bl}} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JArr{V.JBool{bl}}, ind,
        close)) == D1.fixv(D1.own(V.JArr{V.JBool{bl}})) : V.Json}, M4.false_true(h))
    case V.JArr{V.JNum{raw}} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JArr{V.JNum{raw}}, ind,
        close)) == D1.fixv(D1.own(V.JArr{V.JNum{raw}})) : V.Json}, M4.false_true(h))
    case V.JArr{V.JStr{s}} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JArr{V.JStr{s}}, ind,
        close)) == D1.fixv(D1.own(V.JArr{V.JStr{s}})) : V.Json}, M4.false_true(h))
    case V.JArr{V.JSpan{src, n}} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JArr{V.JSpan{src, n}}, ind, close)) == D1.fixv(D1.own(V.JArr{V.JSpan{src,
        n}})) : V.Json}, M4.false_true(h))
    case V.JArr{V.JArr{items}} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JArr{V.JArr{items}}, ind,
        close)) == D1.fixv(D1.own(V.JArr{V.JArr{items}})) : V.Json}, M4.false_true(h))
    case V.JArr{V.JObj{pairs}} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JArr{V.JObj{pairs}}, ind,
        close)) == D1.fixv(D1.own(V.JArr{V.JObj{pairs}})) : V.Json}, M4.false_true(h))
    case V.JArr{V.JNil{}} V.WVal{}:
      {==}
    case V.JArr{V.JCons{+hh, +tt}} V.WVal{}:
      +inner = "  " ++ ind
      eh = pq.left(V.wf.go(hh, V.WVal{}), V.wf.go(tt, V.WArr{}), h)
      et = pq.right(V.wf.go(hh, V.WVal{}), V.wf.go(tt, V.WArr{}), h)
      Equal.cong(V.Json, V.Json, zz => V.JArr{zz}, V.JCons{L2.g.val(pq.g(hh, inner, "")), L2.g.val(pq.g(tt, inner,
        "\n" ++ ind))}, V.JCons{D1.fixv(D1.own(hh)), D1.fixv(D1.own(tt))}, pq.cons2(L2.g.val(pq.g(hh, inner,
        "")), D1.fixv(D1.own(hh)), L2.g.val(pq.g(tt, inner, "\n" ++ ind)), D1.fixv(D1.own(tt)), pq.val(hh,
        inner, "", V.WVal{}, eh), pq.val(tt, inner, "\n" ++ ind, V.WArr{}, et)))
    case V.JArr{V.JPair{k, v, r}} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JArr{V.JPair{k, v, r}}, ind, close)) == D1.fixv(D1.own(V.JArr{V.JPair{k, v,
        r}})) : V.Json}, M4.false_true(h))
    case V.JArr{V.JBind{src, n, v, r}} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JArr{V.JBind{src, n, v, r}}, ind,
        close)) == D1.fixv(D1.own(V.JArr{V.JBind{src, n, v, r}})) : V.Json}, M4.false_true(h))
    case V.JArr{items} V.WArr{}:
      Empty.absurd({L2.g.val(pq.g(V.JArr{items}, ind, close)) == D1.fixv(D1.own(V.JArr{items})) : V.Json},
        M4.false_true(h))
    case V.JArr{items} V.WObj{}:
      Empty.absurd({L2.g.val(pq.g(V.JArr{items}, ind, close)) == D1.fixv(D1.own(V.JArr{items})) : V.Json},
        M4.false_true(h))
    case V.JObj{V.JNull{}} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JObj{V.JNull{}}, ind,
        close)) == D1.fixv(D1.own(V.JObj{V.JNull{}})) : V.Json}, M4.false_true(h))
    case V.JObj{V.JBool{bl}} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JObj{V.JBool{bl}}, ind,
        close)) == D1.fixv(D1.own(V.JObj{V.JBool{bl}})) : V.Json}, M4.false_true(h))
    case V.JObj{V.JNum{raw}} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JObj{V.JNum{raw}}, ind,
        close)) == D1.fixv(D1.own(V.JObj{V.JNum{raw}})) : V.Json}, M4.false_true(h))
    case V.JObj{V.JStr{s}} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JObj{V.JStr{s}}, ind,
        close)) == D1.fixv(D1.own(V.JObj{V.JStr{s}})) : V.Json}, M4.false_true(h))
    case V.JObj{V.JSpan{src, n}} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JObj{V.JSpan{src, n}}, ind, close)) == D1.fixv(D1.own(V.JObj{V.JSpan{src,
        n}})) : V.Json}, M4.false_true(h))
    case V.JObj{V.JArr{items}} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JObj{V.JArr{items}}, ind,
        close)) == D1.fixv(D1.own(V.JObj{V.JArr{items}})) : V.Json}, M4.false_true(h))
    case V.JObj{V.JObj{pairs}} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JObj{V.JObj{pairs}}, ind,
        close)) == D1.fixv(D1.own(V.JObj{V.JObj{pairs}})) : V.Json}, M4.false_true(h))
    case V.JObj{V.JNil{}} V.WVal{}:
      {==}
    case V.JObj{V.JCons{hh, tt}} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JObj{V.JCons{hh, tt}}, ind, close)) == D1.fixv(D1.own(V.JObj{V.JCons{hh,
        tt}})) : V.Json}, M4.false_true(h))
    case V.JObj{V.JPair{+k, +v, +r}} V.WVal{}:
      +inner = "  " ++ ind
      ev = pq.left(V.wf.go(v, V.WVal{}), V.wf.go(r, V.WObj{}), h)
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(r, V.WObj{}), h)
      +kk = k
      Equal.cong(V.Json, V.Json, zz => V.JObj{zz}, V.JPair{D2.spelled(pq.pcs(kk)), L2.g.val(pq.g(v, inner, "")),
        L2.g.val(pq.g(r, inner, "\n" ++ ind))}, V.JPair{D1.fix_str(kk), D1.fixv(D1.own(v)),
        D1.fixv(D1.own(r))}, pq.pair3(D2.spelled(pq.pcs(kk)), D1.fix_str(kk), L2.g.val(pq.g(v, inner, "")),
        D1.fixv(D1.own(v)), L2.g.val(pq.g(r, inner, "\n" ++ ind)), D1.fixv(D1.own(r)), pq.pcs_spelled(kk),
        pq.val(v, inner, "", V.WVal{}, ev),
        pq.val(r, inner, "\n" ++ ind, V.WObj{}, er)))
    case V.JObj{V.JBind{+src, +n, +v, +r}} V.WVal{}:
      +inner = "  " ++ ind
      ev = pq.left(V.wf.go(v, V.WVal{}), V.wf.go(r, V.WObj{}), h)
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(r, V.WObj{}), h)
      +kk = V.span.str(src, n, U32.is_zero(n))
      Equal.cong(V.Json, V.Json, zz => V.JObj{zz}, V.JPair{D2.spelled(pq.pcs(kk)), L2.g.val(pq.g(v, inner, "")),
        L2.g.val(pq.g(r, inner, "\n" ++ ind))}, V.JPair{D1.fix_str(kk), D1.fixv(D1.own(v)),
        D1.fixv(D1.own(r))}, pq.pair3(D2.spelled(pq.pcs(kk)), D1.fix_str(kk), L2.g.val(pq.g(v, inner, "")),
        D1.fixv(D1.own(v)), L2.g.val(pq.g(r, inner, "\n" ++ ind)), D1.fixv(D1.own(r)), pq.pcs_spelled(kk),
        pq.val(v, inner, "", V.WVal{}, ev),
        pq.val(r, inner, "\n" ++ ind, V.WObj{}, er)))
    case V.JObj{pairs} V.WArr{}:
      Empty.absurd({L2.g.val(pq.g(V.JObj{pairs}, ind, close)) == D1.fixv(D1.own(V.JObj{pairs})) : V.Json},
        M4.false_true(h))
    case V.JObj{pairs} V.WObj{}:
      Empty.absurd({L2.g.val(pq.g(V.JObj{pairs}, ind, close)) == D1.fixv(D1.own(V.JObj{pairs})) : V.Json},
        M4.false_true(h))
    case V.JNil{} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JNil{}, ind, close)) == D1.fixv(D1.own(V.JNil{})) : V.Json}, M4.false_true(h))
    case V.JNil{} V.WArr{}:
      {==}
    case V.JNil{} V.WObj{}:
      {==}
    case V.JCons{hh, tt} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JCons{hh, tt}, ind, close)) == D1.fixv(D1.own(V.JCons{hh, tt})) : V.Json},
        M4.false_true(h))
    case V.JCons{+hh, +tt} V.WArr{}:
      eh = pq.left(V.wf.go(hh, V.WVal{}), V.wf.go(tt, V.WArr{}), h)
      et = pq.right(V.wf.go(hh, V.WVal{}), V.wf.go(tt, V.WArr{}), h)
      pq.cons2(L2.g.val(pq.g(hh, ind, "")), D1.fixv(D1.own(hh)), L2.g.val(pq.g(tt, ind, close)),
        D1.fixv(D1.own(tt)), pq.val(hh, ind, "", V.WVal{}, eh), pq.val(tt, ind, close, V.WArr{}, et))
    case V.JCons{hh, tt} V.WObj{}:
      Empty.absurd({L2.g.val(pq.g(V.JCons{hh, tt}, ind, close)) == D1.fixv(D1.own(V.JCons{hh, tt})) : V.Json},
        M4.false_true(h))
    case V.JPair{k, v, r} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JPair{k, v, r}, ind, close)) == D1.fixv(D1.own(V.JPair{k, v, r})) : V.Json},
        M4.false_true(h))
    case V.JPair{k, v, r} V.WArr{}:
      Empty.absurd({L2.g.val(pq.g(V.JPair{k, v, r}, ind, close)) == D1.fixv(D1.own(V.JPair{k, v, r})) : V.Json},
        M4.false_true(h))
    case V.JPair{+k, +v, +r} V.WObj{}:
      ev = pq.left(V.wf.go(v, V.WVal{}), V.wf.go(r, V.WObj{}), h)
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(r, V.WObj{}), h)
      +kk = k
      pq.pair3(D2.spelled(pq.pcs(kk)), D1.fix_str(kk), L2.g.val(pq.g(v, ind, "")), D1.fixv(D1.own(v)),
        L2.g.val(pq.g(r, ind, close)), D1.fixv(D1.own(r)), pq.pcs_spelled(kk), pq.val(v, ind, "", V.WVal{}, ev),
        pq.val(r, ind, close, V.WObj{}, er))
    case V.JBind{src, n, v, r} V.WVal{}:
      Empty.absurd({L2.g.val(pq.g(V.JBind{src, n, v, r}, ind, close)) == D1.fixv(D1.own(V.JBind{src, n, v,
        r})) : V.Json}, M4.false_true(h))
    case V.JBind{src, n, v, r} V.WArr{}:
      Empty.absurd({L2.g.val(pq.g(V.JBind{src, n, v, r}, ind, close)) == D1.fixv(D1.own(V.JBind{src, n, v,
        r})) : V.Json}, M4.false_true(h))
    case V.JBind{+src, +n, +v, +r} V.WObj{}:
      ev = pq.left(V.wf.go(v, V.WVal{}), V.wf.go(r, V.WObj{}), h)
      er = pq.right(V.wf.go(v, V.WVal{}), V.wf.go(r, V.WObj{}), h)
      +kk = V.span.str(src, n, U32.is_zero(n))
      pq.pair3(D2.spelled(pq.pcs(kk)), D1.fix_str(kk), L2.g.val(pq.g(v, ind, "")), D1.fixv(D1.own(v)),
        L2.g.val(pq.g(r, ind, close)), D1.fixv(D1.own(r)), pq.pcs_spelled(kk), pq.val(v, ind, "", V.WVal{}, ev),
        pq.val(r, ind, close, V.WObj{}, er))

# pretty's text is its derivation's text
law pq.text:
  for +val: V.Json
  for +h_wf: {V.wf(val) == True{} : Bool}
  {D2.g.text(pq.g(val, "", "")) ++ "" == Ezjson.pretty(val) : String}

def pq.text(val, h_wf):
  +gg = pq.g(val, "", "")
  Equal.trans(String, D2.g.text(gg) ++ "", M3.gt(gg, ""), Ezjson.pretty(val), M3.gt_eq(gg, ""),
    Equal.trans(String, M3.gt(gg, ""), Ezjson.pretty(val) ++ "", Ezjson.pretty(val),
      Equal.sym(String, Ezjson.pretty(val) ++ "", M3.gt(gg, ""), pq.tl(val, "", "", V.WVal{}, "", h_wf)),
      M4.append_nil(Ezjson.pretty(val))))

def Laws.pretty_parse(val, h_wf, h_s):
  +gg = pq.g(val, "", "")
  +et = pq.text(val, h_wf)
  es = Equal.trans(Bool, D1.short(D2.g.text(gg) ++ ""), D1.short(Ezjson.pretty(val)), True{},
    Equal.cong(String, Bool, zz => D1.short(zz), D2.g.text(gg) ++ "", Ezjson.pretty(val), et), h_s)
  Equal.trans(Maybe<&2, V.Json>, D1.own_m(Ezjson.parse(Ezjson.pretty(val))),
    D1.own_m(Ezjson.parse(D2.g.text(gg) ++ "")), Some{D1.fixv(D1.own(val))},
    Equal.cong(String, Maybe<&2, V.Json>, zz => D1.own_m(Ezjson.parse(zz)), Ezjson.pretty(val),
      D2.g.text(gg) ++ "", Equal.sym(String, D2.g.text(gg) ++ "", Ezjson.pretty(val), et)),
    Equal.trans(Maybe<&2, V.Json>, D1.own_m(Ezjson.parse(D2.g.text(gg) ++ "")), Some{L2.g.val(gg)},
      Some{D1.fixv(D1.own(val))},
      L2.text_some(gg, "", "", pq.ok(val, "", "", V.WVal{}, h_wf, {==}, {==}), {==}, {==}, es),
      Equal.cong(V.Json, Maybe<&2, V.Json>, zz => Some{zz}, L2.g.val(gg), D1.fixv(D1.own(val)),
        pq.val(val, "", "", V.WVal{}, h_wf))))
