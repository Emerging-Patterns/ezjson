# character classes, U32 increments and bounded texts
import Base
import ../../src/value.bend as V
import ../../src/lex.bend as Lex
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ./ArrayLength.bend as M1
import ./LexemeOrder.bend as M2
import ./WellFormedCells.bend as M3

# U32 increment and decrement, bit by bit. Word.adc adds the low bit first;
# with a zero second word it adds or takes away only the carry

# adding the carry then taking it back, from the lowest bit up, is nothing
law adc_inc_dec:
  for +qq: Nat
  for +aw: Word(qq)
  for cc: Bool
  {Word.adc(qq, Word.adc(qq, aw, Word.zero(qq), False{}, cc), Word.zero(qq), True{}, Bool.not(cc)) == aw : Word(qq)}

def adc_inc_dec(qq, aw, cc):
  match qq:
    case 0n:
      match aw:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match aw cc:
        case WCon{False{}, +at} False{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{False{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), False{}, False{}), Word.zero(pp), True{}, True{}), at,
            adc_inc_dec(pp, at, False{}))
        case WCon{True{}, +at} False{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{True{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), False{}, False{}), Word.zero(pp), True{}, True{}), at,
            adc_inc_dec(pp, at, False{}))
        case WCon{False{}, +at} True{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{False{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), False{}, False{}), Word.zero(pp), True{}, True{}), at,
            adc_inc_dec(pp, at, False{}))
        case WCon{True{}, +at} True{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{True{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), False{}, True{}), Word.zero(pp), True{}, False{}), at,
            adc_inc_dec(pp, at, True{}))

# taking the carry away then adding it back, from the lowest bit up, is nothing
law adc_dec_inc:
  for +qq: Nat
  for +aw: Word(qq)
  for cc: Bool
  {Word.adc(qq, Word.adc(qq, aw, Word.zero(qq), True{}, cc), Word.zero(qq), False{}, Bool.not(cc)) == aw : Word(qq)}

def adc_dec_inc(qq, aw, cc):
  match qq:
    case 0n:
      match aw:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match aw cc:
        case WCon{False{}, +at} True{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{False{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), True{}, True{}), Word.zero(pp), False{}, False{}), at,
            adc_dec_inc(pp, at, True{}))
        case WCon{True{}, +at} True{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{True{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), True{}, True{}), Word.zero(pp), False{}, False{}), at,
            adc_dec_inc(pp, at, True{}))
        case WCon{False{}, +at} False{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{False{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), True{}, False{}), Word.zero(pp), False{}, True{}), at,
            adc_dec_inc(pp, at, False{}))
        case WCon{True{}, +at} False{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{True{}, ww},
            Word.adc(pp, Word.adc(pp, at, Word.zero(pp), True{}, True{}), Word.zero(pp), False{}, False{}), at,
            adc_dec_inc(pp, at, True{}))

# one more then one less is the same U32
law u32_dec_inc:
  for +uu: U32
  {U32.sub(U32.add(uu, 1), 1) == uu : U32}

def u32_dec_inc(uu):
  match uu:
    case U32{WCon{False{}, +at}}:
      Equal.cong(Word(31n), U32, ww => U32{WCon{False{}, ww}},
        Word.adc(31n, Word.adc(31n, at, Word.zero(31n), False{}, False{}), Word.zero(31n), True{}, True{}), at,
        adc_inc_dec(31n, at, False{}))
    case U32{WCon{True{}, +at}}:
      Equal.cong(Word(31n), U32, ww => U32{WCon{True{}, ww}},
        Word.adc(31n, Word.adc(31n, at, Word.zero(31n), False{}, True{}), Word.zero(31n), True{}, False{}), at,
        adc_inc_dec(31n, at, True{}))

# one less then one more is the same U32
law u32_inc_dec:
  for +uu: U32
  {U32.add(U32.sub(uu, 1), 1) == uu : U32}

def u32_inc_dec(uu):
  match uu:
    case U32{WCon{False{}, +at}}:
      Equal.cong(Word(31n), U32, ww => U32{WCon{False{}, ww}},
        Word.adc(31n, Word.adc(31n, at, Word.zero(31n), True{}, False{}), Word.zero(31n), False{}, True{}), at,
        adc_dec_inc(31n, at, False{}))
    case U32{WCon{True{}, +at}}:
      Equal.cong(Word(31n), U32, ww => U32{WCon{True{}, ww}},
        Word.adc(31n, Word.adc(31n, at, Word.zero(31n), True{}, True{}), Word.zero(31n), False{}, False{}), at,
        adc_dec_inc(31n, at, True{}))

# one more than a U32 below the top is not zero, once the answer is named
law inc_nonzero.at:
  for +uu: U32
  for bb: Bool
  for eb: {U32.is_zero(U32.add(uu, 1)) == bb : Bool}
  for h_top: {U32.is_eq(uu, 4294967295) == False{} : Bool}
  {U32.is_zero(U32.add(uu, 1)) == False{} : Bool}

def inc_nonzero.at(uu, bb, eb, h_top):
  match bb:
    case False{}:
      eb
    case True{}:
      e0 = M3.ueq(U32.add(uu, 1), 0, eb)
      back = Equal.sym(U32, U32.sub(U32.add(uu, 1), 1), uu, u32_dec_inc(uu))
      down = Equal.cong(U32, U32, xx => U32.sub(xx, 1), U32.add(uu, 1), 0, e0)
      at_top = Equal.trans(U32, uu, U32.sub(U32.add(uu, 1), 1), 4294967295, back, down)
      top = Equal.cong(U32, Bool, xx => U32.is_eq(xx, 4294967295), uu, 4294967295, at_top)
      Empty.absurd({U32.is_zero(U32.add(uu, 1)) == False{} : Bool},
        M1.true_false(Equal.trans(Bool, True{}, U32.is_eq(uu, 4294967295), False{},
          Equal.sym(Bool, U32.is_eq(uu, 4294967295), True{}, top), h_top)))

# one more than a U32 below the top is not zero
law inc_nonzero:
  for +uu: U32
  for h_top: {U32.is_eq(uu, 4294967295) == False{} : Bool}
  {U32.is_zero(U32.add(uu, 1)) == False{} : Bool}

def inc_nonzero(uu, h_top):
  inc_nonzero.at(uu, U32.is_zero(U32.add(uu, 1)), {==}, h_top)

# a U32 compares equal to itself
law u32_eq_refl:
  for +uu: U32
  {U32.is_eq(uu, uu) == True{} : Bool}

def u32_eq_refl(uu):
  match uu:
    case U32{ww}:
      rf = Equal.sym(Cmp, Word.cmp(32n, ww, ww), EQ{}, M3.weq_refl(32n, ww))
      %rf : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# U32s whose predecessors differ differ
law u32_ne_pred:
  for +aa: U32
  for +bb: U32
  for h_ne: {U32.is_eq(U32.sub(aa, 1), U32.sub(bb, 1)) == False{} : Bool}
  for bc: Bool
  for ec: {U32.is_eq(aa, bb) == bc : Bool}
  {U32.is_eq(aa, bb) == False{} : Bool}

def u32_ne_pred(aa, bb, h_ne, bc, ec):
  match bc:
    case False{}:
      ec
    case True{}:
      eab = M3.ueq(aa, bb, ec)
      pre = Equal.cong(U32, Bool, xx => U32.is_eq(U32.sub(aa, 1), U32.sub(xx, 1)), aa, bb, eab)
      same = Equal.trans(Bool, True{}, U32.is_eq(U32.sub(aa, 1), U32.sub(aa, 1)), U32.is_eq(U32.sub(aa, 1),
        U32.sub(bb, 1)),
        Equal.sym(Bool, U32.is_eq(U32.sub(aa, 1), U32.sub(aa, 1)), True{}, u32_eq_refl(U32.sub(aa, 1))), pre)
      Empty.absurd({U32.is_eq(aa, bb) == False{} : Bool},
        M1.true_false(Equal.trans(Bool, True{}, U32.is_eq(U32.sub(aa, 1), U32.sub(bb, 1)), False{}, same, h_ne)))

# SNil, and nothing else
def snil(txt: String) -> Bool:
  match txt:
    case SNil{}:
      True{}
    case SCon{_, _}:
      False{}

# the empty string is no character followed by more
law nil_cons:
  for -cc: Char
  for -rest: String
  for ee: {SNil{} == SCon{cc, rest} : String}
  Empty

def nil_cons(cc, rest, ee):
  M1.true_false(Equal.cong(String, Bool, xx => snil(xx), SNil{}, SCon{cc, rest}, ee))

# zero differs from a U32 that is not zero
law zero_ne:
  for +nn: U32
  for +bb: U32
  for e0: {nn == 0 : U32}
  for h_nz: {Bool.not(U32.is_zero(bb)) == True{} : Bool}
  for bc: Bool
  for ec: {U32.is_eq(nn, bb) == bc : Bool}
  {U32.is_eq(nn, bb) == False{} : Bool}

def zero_ne(nn, bb, e0, h_nz, bc, ec):
  match bc:
    case False{}:
      ec
    case True{}:
      b0 = Equal.trans(U32, bb, nn, 0, Equal.sym(U32, nn, bb, M3.ueq(nn, bb, ec)), e0)
      nz = Equal.cong(U32, Bool, xx => Bool.not(U32.is_zero(xx)), bb, 0, b0)
      Empty.absurd({U32.is_eq(nn, bb) == False{} : Bool},
        M1.true_false(Equal.trans(Bool, True{}, Bool.not(U32.is_zero(bb)), False{}, Equal.sym(Bool,
          Bool.not(U32.is_zero(bb)), True{}, h_nz), nz)))

# pos_ne at the first character: position 0, and bb is not zero
law pos_ne.head:
  for +nn: U32
  for +bb: U32
  for -tl: String
  for e0: {nn == 0 : U32}
  for got: ({Bool.not(U32.is_zero(bb)) == True{} : Bool} & {D1.bounded(tl, U32.sub(bb, 1)) == True{} : Bool})
  {U32.is_eq(nn, bb) == False{} : Bool}

def pos_ne.head(nn, bb, _tl, e0, got):
  (nz, _hb) = got
  zero_ne(nn, bb, e0, nz, U32.is_eq(nn, bb), {==})

# pos_ne past the first character, the rest given
law pos_ne.tail:
  for +nn: U32
  for +bb: U32
  for -tl: String
  for got: ({Bool.not(U32.is_zero(bb)) == True{} : Bool} & {D1.bounded(tl, U32.sub(bb, 1)) == True{} : Bool})
  for ih: {D1.bounded(tl, U32.sub(bb, 1)) == True{} : Bool}
    -> {U32.is_eq(U32.sub(nn, 1), U32.sub(bb, 1)) == False{} : Bool}
  {U32.is_eq(nn, bb) == False{} : Bool}

def pos_ne.tail(nn, bb, _tl, got, ih):
  (_nz, hb) = got
  u32_ne_pred(nn, bb, ih(hb), U32.is_eq(nn, bb), {==})

# a position that holds a character, in a text of at most bb characters, is not bb
law pos_ne:
  for +cut: String
  for +nn: U32
  for +bb: U32
  for zz: Bool
  for ez: {U32.is_zero(nn) == zz : Bool}
  for h_b: {D1.bounded(cut, bb) == True{} : Bool}
  for cc: Char
  for rest: String
  for h_d: {M3.sdrop(cut, nn, zz) == SCon{cc, rest} : String}
  {U32.is_eq(nn, bb) == False{} : Bool}

def pos_ne(cut, nn, bb, zz, ez, h_b, cc, rest, h_d):
  match cut zz:
    case SNil{} True{}:
      Empty.absurd({U32.is_eq(nn, bb) == False{} : Bool}, nil_cons(cc, rest, h_d))
    case SNil{} False{}:
      Empty.absurd({U32.is_eq(nn, bb) == False{} : Bool}, nil_cons(cc, rest, h_d))
    case SCon{hd, tl} True{}:
      pos_ne.head(nn, bb, tl, M3.ueq(nn, 0, ez), M2.and_both(Bool.not(U32.is_zero(bb)), D1.bounded(tl, U32.sub(bb, 1)),
        h_b))
    case SCon{hd, tl} False{}:
      pos_ne.tail(nn, bb, tl, M2.and_both(Bool.not(U32.is_zero(bb)), D1.bounded(tl, U32.sub(bb, 1)), h_b),
        hh => pos_ne(tl, U32.sub(nn, 1), U32.sub(bb, 1), U32.is_zero(U32.sub(nn, 1)), {==}, hh, cc, rest, h_d))

# one less than a nonzero U32 is not the top
law pred_ne_top:
  for +bb: U32
  for h_nz: {Bool.not(U32.is_zero(bb)) == True{} : Bool}
  for bc: Bool
  for ec: {U32.is_eq(U32.sub(bb, 1), 4294967295) == bc : Bool}
  {U32.is_eq(U32.sub(bb, 1), 4294967295) == False{} : Bool}

def pred_ne_top(bb, h_nz, bc, ec):
  match bc:
    case False{}:
      ec
    case True{}:
      et = M3.ueq(U32.sub(bb, 1), 4294967295, ec)
      up = Equal.cong(U32, U32, xx => U32.add(xx, 1), U32.sub(bb, 1), 4294967295, et)
      b0 = Equal.trans(U32, bb, U32.add(U32.sub(bb, 1), 1), 0, Equal.sym(U32, U32.add(U32.sub(bb, 1), 1), bb,
        u32_inc_dec(bb)), up)
      nz = Equal.cong(U32, Bool, xx => Bool.not(U32.is_zero(xx)), bb, 0, b0)
      Empty.absurd({U32.is_eq(U32.sub(bb, 1), 4294967295) == False{} : Bool},
        M1.true_false(Equal.trans(Bool, True{}, Bool.not(U32.is_zero(bb)), False{},
          Equal.sym(Bool, Bool.not(U32.is_zero(bb)), True{}, h_nz), nz)))

# bounded_mono past the first character, the rest given
law bounded_mono.cons:
  for -tl: String
  for +bb: U32
  for h_top: {U32.is_eq(bb, 4294967295) == False{} : Bool}
  for got: ({Bool.not(U32.is_zero(bb)) == True{} : Bool} & {D1.bounded(tl, U32.sub(bb, 1)) == True{} : Bool})
  for ih: {U32.is_eq(U32.sub(bb, 1), 4294967295) == False{} : Bool} -> {D1.bounded(tl, U32.sub(bb,
    1)) == True{} : Bool}
    -> {D1.bounded(tl, U32.add(U32.sub(bb, 1), 1)) == True{} : Bool}
  {Bool.and(Bool.not(U32.is_zero(U32.add(bb, 1))), D1.bounded(tl, U32.sub(U32.add(bb, 1), 1))) == True{} : Bool}

def bounded_mono.cons(tl, bb, h_top, got, ih):
  (nz, hb) = got
  z1 = Equal.sym(Bool, U32.is_zero(U32.add(bb, 1)), False{}, inc_nonzero(bb, h_top))
  %z1 : {Bool.and(Bool.not(_), D1.bounded(tl, U32.sub(U32.add(bb, 1), 1))) == True{} : Bool}
  d1 = Equal.sym(U32, U32.sub(U32.add(bb, 1), 1), bb, u32_dec_inc(bb))
  %d1 : {Bool.and(True{}, D1.bounded(tl, _)) == True{} : Bool}
  i1 = u32_inc_dec(bb)
  %i1 : {Bool.and(True{}, D1.bounded(tl, _)) == True{} : Bool}
  ih(pred_ne_top(bb, nz, U32.is_eq(U32.sub(bb, 1), 4294967295), {==}), hb)

# a text within bb characters is within bb + 1, below the top
law bounded_mono:
  for +txt: String
  for +bb: U32
  for h_top: {U32.is_eq(bb, 4294967295) == False{} : Bool}
  for h_b: {D1.bounded(txt, bb) == True{} : Bool}
  {D1.bounded(txt, U32.add(bb, 1)) == True{} : Bool}

def bounded_mono(txt, bb, h_top, h_b):
  match txt:
    case SNil{}:
      {==}
    case SCon{hd, tl}:
      bounded_mono.cons(tl, bb, h_top, M2.and_both(Bool.not(U32.is_zero(bb)), D1.bounded(tl, U32.sub(bb, 1)), h_b),
        ht => hh => bounded_mono(tl, U32.sub(bb, 1), ht, hh))

# the rest of a short text is short
law short_tail:
  for +hd: Char
  for +tl: String
  for h_s: {D1.short(SCon{hd, tl}) == True{} : Bool}
  {D1.short(tl) == True{} : Bool}

def short_tail(_hd, tl, h_s):
  bounded_mono(tl, 4294967294, {==}, h_s)

# a string without its first character
def rest1(txt: String) -> String:
  match txt:
    case SNil{}:
      SNil{}
    case SCon{_, tl}:
      tl

# a nonzero U32's zero test, as the negation span.str and sdrop need
law nz_of:
  for +nn: U32
  for ez: {U32.is_zero(nn) == False{} : Bool}
  {Bool.not(U32.is_zero(nn)) == True{} : Bool}

def nz_of(nn, ez):
  ee = Equal.sym(Bool, U32.is_zero(nn), False{}, ez)
  %ee : {Bool.not(_) == True{} : Bool}
  {==}

# nothing dropped is the whole string
law sdrop_zero:
  for +txt: String
  for rest: String
  for ee: {txt == rest : String}
  {M3.sdrop(txt, 0, True{}) == rest : String}

def sdrop_zero(txt, _rest, ee):
  match txt:
    case SNil{}:
      ee
    case SCon{_, _}:
      ee

# what is left after a span one longer, past the first character, the rest given
law sdrop_grow.cons:
  for +hd: Char
  for +tl: String
  for +nn: U32
  for h_top: {U32.is_eq(nn, 4294967295) == False{} : Bool}
  for rest: String
  for ih: {M3.sdrop(tl, U32.add(U32.sub(nn, 1), 1), U32.is_zero(U32.add(U32.sub(nn, 1), 1))) == rest : String}
  {M3.sdrop(SCon{hd, tl}, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1))) == rest : String}

def sdrop_grow.cons(hd, tl, nn, h_top, rest, ih):
  z1 = Equal.sym(Bool, U32.is_zero(U32.add(nn, 1)), False{}, inc_nonzero(nn, h_top))
  %z1 : {M3.sdrop(SCon{hd, tl}, U32.add(nn, 1), _) == rest : String}
  d1 = Equal.sym(U32, U32.sub(U32.add(nn, 1), 1), nn, u32_dec_inc(nn))
  %d1 : {M3.sdrop(tl, _, U32.is_zero(_)) == rest : String}
  i1 = u32_inc_dec(nn)
  %i1 : {M3.sdrop(tl, _, U32.is_zero(_)) == rest : String}
  ih

# what is left after a span one longer is what followed its next character
law sdrop_grow:
  for +cut: String
  for +nn: U32
  for zz: Bool
  for +ez: {U32.is_zero(nn) == zz : Bool}
  for h_top: {U32.is_eq(nn, 4294967295) == False{} : Bool}
  for cc: Char
  for +rest: String
  for h_d: {M3.sdrop(cut, nn, zz) == SCon{cc, rest} : String}
  {M3.sdrop(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1))) == rest : String}

def sdrop_grow(cut, nn, zz, ez, h_top, cc, rest, h_d):
  match cut zz:
    case SNil{} True{}:
      Empty.absurd({M3.sdrop(SNil{}, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1))) == rest : String}, nil_cons(cc, rest,
        h_d))
    case SNil{} False{}:
      Empty.absurd({M3.sdrop(SNil{}, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1))) == rest : String}, nil_cons(cc, rest,
        h_d))
    case SCon{hd, tl} True{}:
      e0 = Equal.sym(U32, nn, 0, M3.ueq(nn, 0, ez))
      %e0 : {M3.sdrop(SCon{hd, tl}, U32.add(_, 1), U32.is_zero(U32.add(_, 1))) == rest : String}
      sdrop_zero(tl, rest, Equal.cong(String, String, xx => rest1(xx), SCon{hd, tl}, SCon{cc, rest}, h_d))
    case SCon{hd, tl} False{}:
      sdrop_grow.cons(hd, tl, nn, h_top, rest,
        sdrop_grow(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), {==},
          pred_ne_top(nn, nz_of(nn, ez), U32.is_eq(U32.sub(nn, 1), 4294967295), {==}), cc, rest, h_d))

# WP-L1: the character machine only adds tokens in front of those it is given

# a lexer state with more tokens after its own
def lex.app(lx: Lex.Lex, tt: List<&2, Lex.Tok>) -> Lex.Lex:
  match lx:
    case Lex.Lex{md, bf, tk}:
      Lex.Lex{md, bf, List.append(&2, Lex.Tok, tk, tt)}

# escape.put passes its tokens through
law pass.escape_put:
  for mb: Maybe<&2, Char>
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  {Lex.escape.put(mb, bf, tt) == lex.app(Lex.escape.put(mb, bf, []), tt) : Lex.Lex}

def pass.escape_put(mb, _bf, _tt):
  match mb:
    case Some{_}:
      {==}
    case None{}:
      {==}

# escape.go passes its tokens through
law pass.escape_go:
  for +ch: Char
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  for is_u: Bool
  {Lex.escape.go(ch, bf, tt, is_u) == lex.app(Lex.escape.go(ch, bf, [], is_u), tt) : Lex.Lex}

def pass.escape_go(ch, bf, tt, is_u):
  match is_u:
    case True{}:
      {==}
    case False{}:
      pass.escape_put(Lex.unescape(ch), bf, tt)

# escape passes its tokens through
law pass.escape:
  for +ch: Char
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  {Lex.escape(ch, bf, tt) == lex.app(Lex.escape(ch, bf, []), tt) : Lex.Lex}

def pass.escape(ch, bf, tt):
  pass.escape_go(ch, bf, tt, U32.is_eq(Char.to_u32(ch), 117))

# unicode.end.go passes its tokens through
law pass.end_go:
  for cp: U32
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  for key: Lex.Sur
  {Lex.unicode.end.go(cp, bf, tt, key) == lex.app(Lex.unicode.end.go(cp, bf, [], key), tt) : Lex.Lex}

def pass.end_go(_cp, _bf, _tt, key):
  match key:
    case Lex.SOk{}:
      {==}
    case Lex.SHi{}:
      {==}
    case Lex.SLo{}:
      {==}

# unicode.put passes its tokens through
law pass.put:
  for left: Nat
  for +acc: U32
  for +dig: U32
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  {Lex.unicode.put(left, acc, dig, bf, tt) == lex.app(Lex.unicode.put(left, acc, dig, bf, []), tt) : Lex.Lex}

def pass.put(left, acc, dig, bf, tt):
  match left:
    case 0n:
      pass.end_go((acc * 16 + dig : U32), bf, tt, Lex.unicode.sur((acc * 16 + dig : U32)))
    case 1n+_:
      {==}

# unicode.go passes its tokens through
law pass.uni_go:
  for left: Nat
  for acc: U32
  for ch: Char
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  for ok: Bool
  {Lex.unicode.go(left, acc, ch, bf, tt, ok) == lex.app(Lex.unicode.go(left, acc, ch, bf, [], ok), tt) : Lex.Lex}

def pass.uni_go(left, acc, ch, bf, tt, ok):
  match ok:
    case True{}:
      pass.put(left, acc, Lex.hex(ch), bf, tt)
    case False{}:
      {==}

# unicode.low.end.go passes its tokens through
law pass.low_end_go:
  for lo: U32
  for hi: U32
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  for key: Lex.Sur
  {Lex.unicode.low.end.go(lo, hi, bf, tt, key) == lex.app(Lex.unicode.low.end.go(lo, hi, bf, [], key), tt) : Lex.Lex}

def pass.low_end_go(_lo, _hi, _bf, _tt, key):
  match key:
    case Lex.SLo{}:
      {==}
    case Lex.SOk{}:
      {==}
    case Lex.SHi{}:
      {==}

# unicode.low.put passes its tokens through
law pass.low_put:
  for left: Nat
  for +acc: U32
  for hi: U32
  for +dig: U32
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  {Lex.unicode.low.put(left, acc, hi, dig, bf, tt) == lex.app(Lex.unicode.low.put(left, acc, hi, dig, bf, []),
    tt) : Lex.Lex}

def pass.low_put(left, acc, hi, dig, bf, tt):
  match left:
    case 0n:
      pass.low_end_go((acc * 16 + dig : U32), hi, bf, tt, Lex.unicode.sur((acc * 16 + dig : U32)))
    case 1n+_:
      {==}

# unicode.low.go passes its tokens through
law pass.low_go:
  for left: Nat
  for acc: U32
  for hi: U32
  for ch: Char
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  for ok: Bool
  {Lex.unicode.low.go(left, acc, hi, ch, bf, tt, ok) == lex.app(Lex.unicode.low.go(left, acc, hi, ch, bf, [], ok),
    tt) : Lex.Lex}

def pass.low_go(left, acc, hi, ch, bf, tt, ok):
  match ok:
    case True{}:
      pass.low_put(left, acc, hi, Lex.hex(ch), bf, tt)
    case False{}:
      {==}

# step.str.go passes its tokens through
law pass.str_go:
  for ch: Char
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  for ctrl: Bool
  {Lex.step.str.go(ch, bf, tt, ctrl) == lex.app(Lex.step.str.go(ch, bf, [], ctrl), tt) : Lex.Lex}

def pass.str_go(_ch, _bf, _tt, ctrl):
  match ctrl:
    case True{}:
      {==}
    case False{}:
      {==}

# step.hi.go passes its tokens through
law pass.hi_go:
  for hi: U32
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  for slash: Bool
  {Lex.step.hi.go(hi, bf, tt, slash) == lex.app(Lex.step.hi.go(hi, bf, [], slash), tt) : Lex.Lex}

def pass.hi_go(_hi, _bf, _tt, slash):
  match slash:
    case True{}:
      {==}
    case False{}:
      {==}

# step.hiesc.go passes its tokens through
law pass.hiesc_go:
  for hi: U32
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  for is_u: Bool
  {Lex.step.hiesc.go(hi, bf, tt, is_u) == lex.app(Lex.step.hiesc.go(hi, bf, [], is_u), tt) : Lex.Lex}

def pass.hiesc_go(_hi, _bf, _tt, is_u):
  match is_u:
    case True{}:
      {==}
    case False{}:
      {==}

# step.hiesc passes its tokens through
law pass.hiesc:
  for hi: U32
  for ch: Char
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  {Lex.step.hiesc(hi, ch, bf, tt) == lex.app(Lex.step.hiesc(hi, ch, bf, []), tt) : Lex.Lex}

def pass.hiesc(hi, ch, bf, tt):
  pass.hiesc_go(hi, bf, tt, U32.is_eq(Char.to_u32(ch), 117))

# step passes its tokens through, after the ones it adds
law pass.step:
  for md: Lex.Mode
  for cls: Lex.Class
  for +ch: Char
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  {Lex.step(md, cls, ch, bf, tt) == lex.app(Lex.step(md, cls, ch, bf, []), tt) : Lex.Lex}

def pass.step(md, cls, ch, bf, tt):
  match md cls:
    case Lex.Idle{} Lex.CPunct{_}:
      {==}
    case Lex.Idle{} Lex.CQuote{}:
      {==}
    case Lex.Idle{} Lex.CSpace{}:
      {==}
    case Lex.Idle{} Lex.CBack{}:
      {==}
    case Lex.Idle{} Lex.COther{}:
      {==}
    case Lex.Word{} Lex.CPunct{_}:
      {==}
    case Lex.Word{} Lex.CQuote{}:
      {==}
    case Lex.Word{} Lex.CSpace{}:
      {==}
    case Lex.Word{} Lex.CBack{}:
      {==}
    case Lex.Word{} Lex.COther{}:
      {==}
    case Lex.Str{} Lex.CQuote{}:
      {==}
    case Lex.Str{} Lex.CBack{}:
      {==}
    case Lex.Str{} Lex.CPunct{_}:
      pass.str_go(ch, bf, tt, U32.is_lt(Char.to_u32(ch), 32))
    case Lex.Str{} Lex.CSpace{}:
      pass.str_go(ch, bf, tt, U32.is_lt(Char.to_u32(ch), 32))
    case Lex.Str{} Lex.COther{}:
      pass.str_go(ch, bf, tt, U32.is_lt(Char.to_u32(ch), 32))
    case Lex.Esc{} _:
      pass.escape(ch, bf, tt)
    case Lex.Uni{left, acc} _:
      pass.uni_go(left, acc, ch, bf, tt, Lex.hex.ok(Char.to_u32(ch)))
    case Lex.Hi{hi} _:
      pass.hi_go(hi, bf, tt, U32.is_eq(Char.to_u32(ch), 92))
    case Lex.HiEsc{hi} _:
      pass.hiesc(hi, ch, bf, tt)
    case Lex.Lo{left, acc, hi} _:
      pass.low_go(left, acc, hi, ch, bf, tt, Lex.hex.ok(Char.to_u32(ch)))
    case Lex.Bad{} _:
      {==}

# feed passes its tokens through, after the ones it adds
law pass.feed:
  for +ch: Char
  for md: Lex.Mode
  for bf: List<&2, Char>
  for tt: List<&2, Lex.Tok>
  {Lex.feed(ch, Lex.Lex{md, bf, tt}) == lex.app(Lex.feed(ch, Lex.Lex{md, bf, []}), tt) : Lex.Lex}

def pass.feed(ch, md, bf, tt):
  pass.step(md, Lex.classify(ch), ch, bf, tt)

# a lexer state with its tokens' spans replaced
def dlex(lx: Lex.Lex) -> Lex.Lex:
  match lx:
    case Lex.Lex{md, bf, tk}:
      Lex.Lex{md, bf, M2.dens(tk)}

# replacing spans goes through an append
law dens_app:
  for +aa: List<&2, Lex.Tok>
  for bb: List<&2, Lex.Tok>
  {M2.dens(List.append(&2, Lex.Tok, aa, bb)) == List.append(&2, Lex.Tok, M2.dens(aa), M2.dens(bb)) : List<&2, Lex.Tok>}

def dens_app(aa, bb):
  match aa:
    case Nil{}:
      {==}
    case hd <> tl:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, xx => M2.den(hd) <> xx,
        M2.dens(List.append(&2, Lex.Tok, tl, bb)), List.append(&2, Lex.Tok, M2.dens(tl), M2.dens(bb)), dens_app(tl, bb))

# replacing spans goes through a reversal
law dens_rev:
  for +aa: List<&2, Lex.Tok>
  for acc: List<&2, Lex.Tok>
  {M2.dens(List.reverse.go(&2, Lex.Tok, aa, acc)) == List.reverse.go(&2, Lex.Tok, M2.dens(aa), M2.dens(acc)) : List<&2,
      Lex.Tok>}

def dens_rev(aa, acc):
  match aa:
    case Nil{}:
      {==}
    case hd <> tl:
      dens_rev(tl, hd <> acc)

# replacing spans goes through lex.app
law dlex_app:
  for lx: Lex.Lex
  for tt: List<&2, Lex.Tok>
  {dlex(lex.app(lx, tt)) == lex.app(dlex(lx), M2.dens(tt)) : Lex.Lex}

def dlex_app(lx, tt):
  match lx:
    case Lex.Lex{md, bf, tk}:
      Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{md, bf, xx},
        M2.dens(List.append(&2, Lex.Tok, tk, tt)), List.append(&2, Lex.Tok, M2.dens(tk), M2.dens(tt)), dens_app(tk, tt))

# the tokens a finished lexer gives, with spans replaced, depend only on its
# state with spans replaced
law dens_finish:
  for lx: Lex.Lex
  {M2.dens(Lex.finish(lx)) == Lex.finish(dlex(lx)) : List<&2, Lex.Tok>}

def dens_finish(lx):
  match lx:
    case Lex.Lex{Lex.Idle{}, bf, tk}:
      dens_rev(tk, [])
    case Lex.Lex{Lex.Word{}, bf, tk}:
      dens_rev(Lex.TWord{Lex.text(bf)} <> tk, [])
    case Lex.Lex{Lex.Str{}, bf, tk}:
      dens_rev(Lex.TBad{} <> tk, [])
    case Lex.Lex{Lex.Esc{}, bf, tk}:
      dens_rev(Lex.TBad{} <> tk, [])
    case Lex.Lex{Lex.Uni{_, _}, bf, tk}:
      dens_rev(Lex.TBad{} <> tk, [])
    case Lex.Lex{Lex.Hi{_}, bf, tk}:
      dens_rev(Lex.TBad{} <> tk, [])
    case Lex.Lex{Lex.HiEsc{_}, bf, tk}:
      dens_rev(Lex.TBad{} <> tk, [])
    case Lex.Lex{Lex.Lo{_, _, _}, bf, tk}:
      dens_rev(Lex.TBad{} <> tk, [])
    case Lex.Lex{Lex.Bad{}, bf, tk}:
      dens_rev(Lex.TBad{} <> tk, [])

# feed as a function of a lexer state with its spans replaced
def feedg(+ch: Char, lx: Lex.Lex) -> Lex.Lex:
  match lx:
    case Lex.Lex{md, bf, dd}:
      lex.app(dlex(Lex.feed(ch, Lex.Lex{md, bf, []})), dd)

# feeding, then replacing spans, is feedg of the replaced state
law dlex_feed_g:
  for +ch: Char
  for +lx: Lex.Lex
  {dlex(Lex.feed(ch, lx)) == feedg(ch, dlex(lx)) : Lex.Lex}

def dlex_feed_g(ch, lx):
  match lx:
    case Lex.Lex{md, bf, tk}:
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, Lex.Lex{md, bf, tk})), dlex(lex.app(Lex.feed(ch, Lex.Lex{md, bf, []}),
        tk)),
        lex.app(dlex(Lex.feed(ch, Lex.Lex{md, bf, []})), M2.dens(tk)),
        Equal.cong(Lex.Lex, Lex.Lex, xx => dlex(xx), Lex.feed(ch, Lex.Lex{md, bf, tk}),
          lex.app(Lex.feed(ch, Lex.Lex{md, bf, []}), tk), pass.feed(ch, md, bf, tk)),
        dlex_app(Lex.feed(ch, Lex.Lex{md, bf, []}), tk))

# two lexer states the same up to spans stay so after one character
law dlex_feed:
  for +ch: Char
  for +l1: Lex.Lex
  for +l2: Lex.Lex
  for ee: {dlex(l1) == dlex(l2) : Lex.Lex}
  {dlex(Lex.feed(ch, l1)) == dlex(Lex.feed(ch, l2)) : Lex.Lex}

def dlex_feed(ch, l1, l2, ee):
  Equal.trans(Lex.Lex, dlex(Lex.feed(ch, l1)), feedg(ch, dlex(l2)), dlex(Lex.feed(ch, l2)),
    Equal.trans(Lex.Lex, dlex(Lex.feed(ch, l1)), feedg(ch, dlex(l1)), feedg(ch, dlex(l2)),
      dlex_feed_g(ch, l1), Equal.cong(Lex.Lex, Lex.Lex, xx => feedg(ch, xx), dlex(l1), dlex(l2), ee)),
    Equal.sym(Lex.Lex, dlex(Lex.feed(ch, l2)), feedg(ch, dlex(l2)), dlex_feed_g(ch, l2)))

# a reversed prefix of no characters is the accumulator
law rev_zero:
  for +src: String
  for +nn: U32
  for acc: List<&2, Char>
  {Lex.tokens.rev(src, nn, True{}, acc) == acc : List<&2, Char>}

def rev_zero(src, _nn, _acc):
  match src:
    case SNil{}:
      {==}
    case SCon{_, _}:
      {==}

# a span of no characters is empty, whatever the count
law span_true:
  for +src: String
  for +nn: U32
  {V.span.str(src, nn, True{}) == "" : String}

def span_true(src, _nn):
  match src:
    case SNil{}:
      {==}
    case SCon{_, _}:
      {==}

# reading a reversed prefix back gives the span's characters, in order
law text_rev:
  for +src: String
  for +nn: U32
  for zz: Bool
  for acc: List<&2, Char>
  for aa: String
  {Lex.text.go(Lex.tokens.rev(src, nn, zz, acc), aa) == Lex.text.go(acc, V.span.str(src, nn, zz) ++ aa) : String}

def text_rev(src, nn, zz, acc, aa):
  match src zz:
    case ss True{}:
      rz = Equal.sym(List<&2, Char>, Lex.tokens.rev(ss, nn, True{}, acc), acc, rev_zero(ss, nn, acc))
      %rz : {Lex.text.go(_, aa) == Lex.text.go(acc, V.span.str(ss, nn, True{}) ++ aa) : String}
      st = Equal.sym(String, V.span.str(ss, nn, True{}), "", span_true(ss, nn))
      %st : {Lex.text.go(acc, aa) == Lex.text.go(acc, _ ++ aa) : String}
      {==}
    case SNil{} False{}:
      {==}
    case SCon{hd, tl} False{}:
      text_rev(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), hd <> acc, aa)

# the text of a reversed prefix is the span
law text_span:
  for +src: String
  for +nn: U32
  for +zz: Bool
  {Lex.text(Lex.tokens.rev(src, nn, zz, [])) == V.span.str(src, nn, zz) : String}

def text_span(src, nn, zz):
  Equal.trans(String, Lex.text(Lex.tokens.rev(src, nn, zz, [])), V.span.str(src, nn, zz) ++ "", V.span.str(src, nn, zz),
    text_rev(src, nn, zz, [], ""), M2.append_nil(V.span.str(src, nn, zz)))

# the first character of a string, or U+0000
def head0(txt: String) -> Char:
  match txt:
    case SNil{}:
      Char.from_u32(0)
    case SCon{hd, _}:
      hd

# a reversed prefix one longer, past the first character, the rest given
law rev_grow.cons:
  for +hd: Char
  for +tl: String
  for +nn: U32
  for h_top: {U32.is_eq(nn, 4294967295) == False{} : Bool}
  for cc: Char
  for +acc: List<&2, Char>
  for ih: {Lex.tokens.rev(tl, U32.add(U32.sub(nn, 1), 1), U32.is_zero(U32.add(U32.sub(nn, 1), 1)), hd <> acc)
    == cc <> Lex.tokens.rev(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), hd <> acc) : List<&2, Char>}
  {Lex.tokens.rev(SCon{hd, tl}, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), acc)
    == cc <> Lex.tokens.rev(SCon{hd, tl}, nn, False{}, acc) : List<&2, Char>}

def rev_grow.cons(hd, tl, nn, h_top, cc, acc, ih):
  z1 = Equal.sym(Bool, U32.is_zero(U32.add(nn, 1)), False{}, inc_nonzero(nn, h_top))
  %z1 : {Lex.tokens.rev(SCon{hd, tl}, U32.add(nn, 1), _, acc)
    == cc <> Lex.tokens.rev(SCon{hd, tl}, nn, False{}, acc) : List<&2, Char>}
  d1 = Equal.sym(U32, U32.sub(U32.add(nn, 1), 1), nn, u32_dec_inc(nn))
  %d1 : {Lex.tokens.rev(tl, _, U32.is_zero(_), hd <> acc)
    == cc <> Lex.tokens.rev(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), hd <> acc) : List<&2, Char>}
  i1 = u32_inc_dec(nn)
  %i1 : {Lex.tokens.rev(tl, _, U32.is_zero(_), hd <> acc)
    == cc <> Lex.tokens.rev(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), hd <> acc) : List<&2, Char>}
  ih

# a reversed prefix one longer is the next character in front, below the top
law rev_grow:
  for +cut: String
  for +nn: U32
  for zz: Bool
  for +ez: {U32.is_zero(nn) == zz : Bool}
  for h_top: {U32.is_eq(nn, 4294967295) == False{} : Bool}
  for +cc: Char
  for rest: String
  for h_d: {M3.sdrop(cut, nn, zz) == SCon{cc, rest} : String}
  for +acc: List<&2, Char>
  {Lex.tokens.rev(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), acc)
    == cc <> Lex.tokens.rev(cut, nn, zz, acc) : List<&2, Char>}

def rev_grow(cut, nn, zz, ez, h_top, cc, rest, h_d, acc):
  match cut zz:
    case SNil{} True{}:
      Empty.absurd({Lex.tokens.rev(SNil{}, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), acc)
        == cc <> Lex.tokens.rev(SNil{}, nn, True{}, acc) : List<&2, Char>}, nil_cons(cc, rest, h_d))
    case SNil{} False{}:
      Empty.absurd({Lex.tokens.rev(SNil{}, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), acc)
        == cc <> Lex.tokens.rev(SNil{}, nn, False{}, acc) : List<&2, Char>}, nil_cons(cc, rest, h_d))
    case SCon{hd, tl} True{}:
      e0 = Equal.sym(U32, nn, 0, M3.ueq(nn, 0, ez))
      %e0 : {Lex.tokens.rev(SCon{hd, tl}, U32.add(_, 1), U32.is_zero(U32.add(_, 1)), acc) == cc <> acc : List<&2, Char>}
      rz = Equal.sym(List<&2, Char>, Lex.tokens.rev(tl, 0, True{}, hd <> acc), hd <> acc, rev_zero(tl, 0, hd <> acc))
      %rz : {_ == cc <> acc : List<&2, Char>}
      Equal.cong(Char, List<&2, Char>, xx => xx <> acc, hd, cc,
        Equal.cong(String, Char, xx => head0(xx), SCon{hd, tl}, SCon{cc, rest}, h_d))
    case SCon{hd, tl} False{}:
      rev_grow.cons(hd, tl, nn, h_top, cc, acc,
        rev_grow(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), {==},
          pred_ne_top(nn, nz_of(nn, ez), U32.is_eq(U32.sub(nn, 1), 4294967295), {==}), cc, rest, h_d, hd <> acc))

# whether a class is Lex.CQuote{}
def is_quote(cls: Lex.Class) -> Bool:
  match cls:
    case Lex.CQuote{}:
      True{}
    case _:
      False{}

# the last test of classify: a character past them all is COther, not Lex.CQuote{}
law cls_quote_end:
  for +cp: U32
  for h_c: {Lex.COther{} == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_end(cp, h_c):
  Empty.absurd({cp == 34 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx), Lex.COther{},
    Lex.CQuote{}, h_c)))

# classify's test for 9, once its answer is named
law cls_quote_11:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 9) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Lex.COther{}) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_11(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx), Lex.CSpace{},
        Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_end(cp, h_c)

# classify's test for 13, once its answer is named
law cls_quote_10:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 13) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
    Lex.COther{})) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_10(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx), Lex.CSpace{},
        Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_11(cp, U32.is_eq(cp, 9), {==}, h_c)

# classify's test for 10, once its answer is named
law cls_quote_9:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 10) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_9(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx), Lex.CSpace{},
        Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_10(cp, U32.is_eq(cp, 13), {==}, h_c)

# classify's test for 32, once its answer is named
law cls_quote_8:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 32) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
      Lex.COther{})))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_8(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx), Lex.CSpace{},
        Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_9(cp, U32.is_eq(cp, 10), {==}, h_c)

# classify's test for 92, once its answer is named
law cls_quote_7:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 92) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
      Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_7(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx), Lex.CBack{},
        Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_8(cp, U32.is_eq(cp, 32), {==}, h_c)

# classify's test for 34, once its answer is named
law cls_quote_6:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 34) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{},
      Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
        Lex.COther{})))))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_6(cp, bb, eb, h_c):
  match bb:
    case True{}:
      M3.ueq(cp, 34, eb)
    case False{}:
      cls_quote_7(cp, U32.is_eq(cp, 92), {==}, h_c)

# classify's test for 44, once its answer is named
law cls_quote_5:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 44) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{},
      Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
        Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))))))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_5(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx),
        Lex.CPunct{Lex.TComma{}}, Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_6(cp, U32.is_eq(cp, 34), {==}, h_c)

# classify's test for 58, once its answer is named
law cls_quote_4:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 58) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44),
    Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class,
      U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class,
        U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class,
          U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{})))))))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_4(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx),
        Lex.CPunct{Lex.TColon{}}, Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_5(cp, U32.is_eq(cp, 44), {==}, h_c)

# classify's test for 125, once its answer is named
law cls_quote_3:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 125) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 58),
    Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class,
      U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class,
        U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class,
          U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
            Lex.COther{}))))))))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_3(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx),
        Lex.CPunct{Lex.TCloseObj{}}, Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_4(cp, U32.is_eq(cp, 58), {==}, h_c)

# classify's test for 123, once its answer is named
law cls_quote_2:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 123) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TOpenObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 125),
    Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 58), Lex.CPunct{Lex.TColon{}},
      Bool.pick(Lex.Class, U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34),
        Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32),
          Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13),
            Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
              Lex.COther{})))))))))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_2(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx),
        Lex.CPunct{Lex.TOpenObj{}}, Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_3(cp, U32.is_eq(cp, 125), {==}, h_c)

# classify's test for 93, once its answer is named
law cls_quote_1:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 93) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TCloseArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 123),
    Lex.CPunct{Lex.TOpenObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 125), Lex.CPunct{Lex.TCloseObj{}},
      Bool.pick(Lex.Class, U32.is_eq(cp, 58), Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44),
        Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class,
          U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class,
            U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
              Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))))))))))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_1(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx),
        Lex.CPunct{Lex.TCloseArr{}}, Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_2(cp, U32.is_eq(cp, 123), {==}, h_c)

# classify's test for 91, once its answer is named
law cls_quote_0:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 91) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TOpenArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 93),
    Lex.CPunct{Lex.TCloseArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 123), Lex.CPunct{Lex.TOpenObj{}},
      Bool.pick(Lex.Class, U32.is_eq(cp, 125), Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 58),
        Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}},
          Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{},
            Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10),
              Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp,
                9), Lex.CSpace{}, Lex.COther{})))))))))))) == Lex.CQuote{} : Lex.Class}
  {cp == 34 : U32}

def cls_quote_0(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 34 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_quote(xx),
        Lex.CPunct{Lex.TOpenArr{}}, Lex.CQuote{}, h_c)))
    case False{}:
      cls_quote_1(cp, U32.is_eq(cp, 93), {==}, h_c)

# a character classify reads as Lex.CQuote{} is code point 34
law cls_quote:
  for +ch: Char
  for h_c: {Lex.classify(ch) == Lex.CQuote{} : Lex.Class}
  {Char.to_u32(ch) == 34 : U32}

def cls_quote(ch, h_c):
  cls_quote_0(Char.to_u32(ch), U32.is_eq(Char.to_u32(ch), 91), {==}, h_c)

# whether a class is Lex.CBack{}
def is_back(cls: Lex.Class) -> Bool:
  match cls:
    case Lex.CBack{}:
      True{}
    case _:
      False{}

# the last test of classify: a character past them all is COther, not Lex.CBack{}
law cls_back_end:
  for +cp: U32
  for h_c: {Lex.COther{} == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_end(cp, h_c):
  Empty.absurd({cp == 92 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx), Lex.COther{}, Lex.CBack{},
    h_c)))

# classify's test for 9, once its answer is named
law cls_back_11:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 9) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Lex.COther{}) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_11(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx), Lex.CSpace{},
        Lex.CBack{}, h_c)))
    case False{}:
      cls_back_end(cp, h_c)

# classify's test for 13, once its answer is named
law cls_back_10:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 13) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
    Lex.COther{})) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_10(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx), Lex.CSpace{},
        Lex.CBack{}, h_c)))
    case False{}:
      cls_back_11(cp, U32.is_eq(cp, 9), {==}, h_c)

# classify's test for 10, once its answer is named
law cls_back_9:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 10) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_9(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx), Lex.CSpace{},
        Lex.CBack{}, h_c)))
    case False{}:
      cls_back_10(cp, U32.is_eq(cp, 13), {==}, h_c)

# classify's test for 32, once its answer is named
law cls_back_8:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 32) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
      Lex.COther{})))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_8(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx), Lex.CSpace{},
        Lex.CBack{}, h_c)))
    case False{}:
      cls_back_9(cp, U32.is_eq(cp, 10), {==}, h_c)

# classify's test for 92, once its answer is named
law cls_back_7:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 92) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
      Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_7(cp, bb, eb, h_c):
  match bb:
    case True{}:
      M3.ueq(cp, 92, eb)
    case False{}:
      cls_back_8(cp, U32.is_eq(cp, 32), {==}, h_c)

# classify's test for 34, once its answer is named
law cls_back_6:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 34) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{},
      Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
        Lex.COther{})))))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_6(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx), Lex.CQuote{},
        Lex.CBack{}, h_c)))
    case False{}:
      cls_back_7(cp, U32.is_eq(cp, 92), {==}, h_c)

# classify's test for 44, once its answer is named
law cls_back_5:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 44) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{},
    Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{},
      Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
        Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))))))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_5(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx),
        Lex.CPunct{Lex.TComma{}}, Lex.CBack{}, h_c)))
    case False{}:
      cls_back_6(cp, U32.is_eq(cp, 34), {==}, h_c)

# classify's test for 58, once its answer is named
law cls_back_4:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 58) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44),
    Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class,
      U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class,
        U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class,
          U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{})))))))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_4(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx),
        Lex.CPunct{Lex.TColon{}}, Lex.CBack{}, h_c)))
    case False{}:
      cls_back_5(cp, U32.is_eq(cp, 44), {==}, h_c)

# classify's test for 125, once its answer is named
law cls_back_3:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 125) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 58),
    Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class,
      U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class,
        U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class,
          U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
            Lex.COther{}))))))))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_3(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx),
        Lex.CPunct{Lex.TCloseObj{}}, Lex.CBack{}, h_c)))
    case False{}:
      cls_back_4(cp, U32.is_eq(cp, 58), {==}, h_c)

# classify's test for 123, once its answer is named
law cls_back_2:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 123) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TOpenObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 125),
    Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 58), Lex.CPunct{Lex.TColon{}},
      Bool.pick(Lex.Class, U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34),
        Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32),
          Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13),
            Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{},
              Lex.COther{})))))))))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_2(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx),
        Lex.CPunct{Lex.TOpenObj{}}, Lex.CBack{}, h_c)))
    case False{}:
      cls_back_3(cp, U32.is_eq(cp, 125), {==}, h_c)

# classify's test for 93, once its answer is named
law cls_back_1:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 93) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TCloseArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 123),
    Lex.CPunct{Lex.TOpenObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 125), Lex.CPunct{Lex.TCloseObj{}},
      Bool.pick(Lex.Class, U32.is_eq(cp, 58), Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44),
        Lex.CPunct{Lex.TComma{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class,
          U32.is_eq(cp, 92), Lex.CBack{}, Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class,
            U32.is_eq(cp, 10), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{},
              Bool.pick(Lex.Class, U32.is_eq(cp, 9), Lex.CSpace{}, Lex.COther{}))))))))))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_1(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx),
        Lex.CPunct{Lex.TCloseArr{}}, Lex.CBack{}, h_c)))
    case False{}:
      cls_back_2(cp, U32.is_eq(cp, 123), {==}, h_c)

# classify's test for 91, once its answer is named
law cls_back_0:
  for +cp: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, 91) == bb : Bool}
  for h_c: {Bool.pick(Lex.Class, bb, Lex.CPunct{Lex.TOpenArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 93),
    Lex.CPunct{Lex.TCloseArr{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 123), Lex.CPunct{Lex.TOpenObj{}},
      Bool.pick(Lex.Class, U32.is_eq(cp, 125), Lex.CPunct{Lex.TCloseObj{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 58),
        Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, U32.is_eq(cp, 44), Lex.CPunct{Lex.TComma{}},
          Bool.pick(Lex.Class, U32.is_eq(cp, 34), Lex.CQuote{}, Bool.pick(Lex.Class, U32.is_eq(cp, 92), Lex.CBack{},
            Bool.pick(Lex.Class, U32.is_eq(cp, 32), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 10),
              Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp, 13), Lex.CSpace{}, Bool.pick(Lex.Class, U32.is_eq(cp,
                9), Lex.CSpace{}, Lex.COther{})))))))))))) == Lex.CBack{} : Lex.Class}
  {cp == 92 : U32}

def cls_back_0(cp, bb, _eb, h_c):
  match bb:
    case True{}:
      Empty.absurd({cp == 92 : U32}, M2.false_true(Equal.cong(Lex.Class, Bool, xx => is_back(xx),
        Lex.CPunct{Lex.TOpenArr{}}, Lex.CBack{}, h_c)))
    case False{}:
      cls_back_1(cp, U32.is_eq(cp, 93), {==}, h_c)

# a character classify reads as Lex.CBack{} is code point 92
law cls_back:
  for +ch: Char
  for h_c: {Lex.classify(ch) == Lex.CBack{} : Lex.Class}
  {Char.to_u32(ch) == 92 : U32}

def cls_back(ch, h_c):
  cls_back_0(Char.to_u32(ch), U32.is_eq(Char.to_u32(ch), 91), {==}, h_c)

# WP-L1: the span scanner against the character machine. rel says what a
# scanner state and a lexer state have in common: the same tokens up to
# spans, and a span that holds exactly the reversed buffer

# rel for a span scanner state, by its mode
def rel.go(+cut: String, +nn: U32, md: Lex.Span, +toks: List<&2, Lex.Tok>, lx: Lex.Lex, ss: String) -> Type:
  match md:
    case Lex.GIdle{}:
      {dlex(lx) == Lex.Lex{Lex.Idle{}, [], M2.dens(toks)} : Lex.Lex}
    case Lex.GWord{}:
      ({dlex(lx) == Lex.Lex{Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), M2.dens(toks)} : Lex.Lex}
        & ({M3.sdrop(cut, nn, U32.is_zero(nn)) == ss : String} & {D1.short(cut) == True{} : Bool}))
    case Lex.GStr{}:
      ({dlex(lx) == Lex.Lex{Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), M2.dens(toks)} : Lex.Lex}
        & ({M3.sdrop(cut, nn, U32.is_zero(nn)) == ss : String} & {D1.short(cut) == True{} : Bool}))
    case Lex.GBad{}:
      {dlex(lx) == Lex.Lex{Lex.Bad{}, [], M2.dens(toks)} : Lex.Lex}

# what a span scanner state and a lexer state share, with `ss` left to read
def rel(sc: Lex.Scan, lx: Lex.Lex, ss: String) -> Type:
  match sc:
    case Lex.Go{cut, nn, md, toks}:
      rel.go(cut, nn, md, toks, lx, ss)
    case Lex.Old{ol}:
      {dlex(lx) == dlex(ol) : Lex.Lex}

# a lexer state the same as Lex{md, bf, tk} up to spans, fed one character
law via:
  for +ch: Char
  for +lx: Lex.Lex
  for +md: Lex.Mode
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for cls: Lex.Class
  for ecls: {Lex.classify(ch) == cls : Lex.Class}
  for hr: {dlex(lx) == Lex.Lex{md, bf, M2.dens(tk)} : Lex.Lex}
  {dlex(Lex.feed(ch, lx)) == dlex(Lex.step(md, cls, ch, bf, tk)) : Lex.Lex}

def via(ch, lx, md, bf, tk, cls, ecls, hr):
  Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), dlex(Lex.feed(ch, Lex.Lex{md, bf, tk})), dlex(Lex.step(md, cls, ch,
    bf, tk)),
    dlex_feed(ch, lx, Lex.Lex{md, bf, tk}, hr),
    Equal.cong(Lex.Lex, Lex.Lex, xx => dlex(xx), Lex.feed(ch, Lex.Lex{md, bf, tk}), Lex.step(md, cls, ch, bf, tk),
      M2.feed_as(ch, md, bf, tk, cls, ecls)))

# step.str, with the control test named
law str_as:
  for +ch: Char
  for bf: List<&2, Char>
  for tk: List<&2, Lex.Tok>
  for ctl: Bool
  for ectl: {U32.is_lt(Char.to_u32(ch), 32) == ctl : Bool}
  {Lex.step.str(ch, bf, tk) == Lex.step.str.go(ch, bf, tk, ctl) : Lex.Lex}

def str_as(ch, bf, tk, ctl, ectl):
  ec = Equal.sym(Bool, U32.is_lt(Char.to_u32(ch), 32), ctl, ectl)
  %ec : {Lex.step.str.go(ch, bf, tk, _) == Lex.step.str.go(ch, bf, tk, ctl) : Lex.Lex}
  {==}

# a quote or a backslash is not a control character
law not_ctl:
  for +ch: Char
  for kk: U32
  for ek: {Char.to_u32(ch) == kk : U32}
  for h_kk: {U32.is_lt(kk, 32) == False{} : Bool}
  for ectl: {U32.is_lt(Char.to_u32(ch), 32) == True{} : Bool}
  Empty

def not_ctl(ch, kk, ek, h_kk, ectl):
  lt = Equal.cong(U32, Bool, xx => U32.is_lt(xx, 32), Char.to_u32(ch), kk, ek)
  M1.true_false(Equal.trans(Bool, True{}, U32.is_lt(kk, 32), False{},
    Equal.trans(Bool, True{}, U32.is_lt(Char.to_u32(ch), 32), U32.is_lt(kk, 32), Equal.sym(Bool,
      U32.is_lt(Char.to_u32(ch), 32), True{}, ectl), lt),
    h_kk))

# a word or string span grown by one character, from the step's lexer state
law grow_rel:
  for +ch: Char
  for +tl: String
  for +cut: String
  for +nn: U32
  for +toks: List<&2, Lex.Tok>
  for -lx: Lex.Lex
  for +md: Lex.Mode
  for +hd: {M3.sdrop(cut, nn, U32.is_zero(nn)) == SCon{ch, tl} : String}
  for +hs: {D1.short(cut) == True{} : Bool}
  for hf: {dlex(Lex.feed(ch, lx)) == Lex.Lex{md, ch <> Lex.tokens.rev(cut, nn, U32.is_zero(nn), []),
    M2.dens(toks)} : Lex.Lex}
  ({dlex(Lex.feed(ch, lx)) == Lex.Lex{md, Lex.tokens.rev(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), []),
    M2.dens(toks)} : Lex.Lex}
    & ({M3.sdrop(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1))) == tl : String} & {D1.short(cut) == True{} : Bool}))

def grow_rel(ch, tl, cut, nn, toks, lx, md, hd, hs, hf):
  +top = pos_ne(cut, nn, 4294967295, U32.is_zero(nn), {==}, hs, ch, tl, hd)
  rg = rev_grow(cut, nn, U32.is_zero(nn), {==}, top, ch, tl, hd, [])
  (Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{md, ch <> Lex.tokens.rev(cut, nn, U32.is_zero(nn), []),
    M2.dens(toks)},
      Lex.Lex{md, Lex.tokens.rev(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), []), M2.dens(toks)}, hf,
      Equal.cong(List<&2, Char>, Lex.Lex, xx => Lex.Lex{md, xx, M2.dens(toks)}, ch <> Lex.tokens.rev(cut, nn,
        U32.is_zero(nn), []),
        Lex.tokens.rev(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), []),
        Equal.sym(List<&2, Char>, Lex.tokens.rev(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), []),
          ch <> Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), rg))),
    (sdrop_grow(cut, nn, U32.is_zero(nn), {==}, top, ch, tl, hd), hs))

# a string opened after a word: its empty buffer, and the word's span as text
law two_cong:
  for +tl: String
  for aa: String
  for bb: String
  for ee: {aa == bb : String}
  for +toks: List<&2, Lex.Tok>
  {Lex.Lex{Lex.Str{}, [], Lex.TWord{aa} <> M2.dens(toks)} == Lex.Lex{Lex.Str{}, Lex.tokens.rev(tl, 0, True{}, []),
    Lex.TWord{bb} <> M2.dens(toks)}
    : Lex.Lex}

def two_cong(tl, aa, bb, ee, toks):
  rz = Equal.sym(List<&2, Char>, Lex.tokens.rev(tl, 0, True{}, []), [], rev_zero(tl, 0, []))
  %rz : {Lex.Lex{Lex.Str{}, [], Lex.TWord{aa} <> M2.dens(toks)} == Lex.Lex{Lex.Str{}, _,
    Lex.TWord{bb} <> M2.dens(toks)} : Lex.Lex}
  %ee : {Lex.Lex{Lex.Str{}, [], Lex.TWord{aa} <> M2.dens(toks)} == Lex.Lex{Lex.Str{}, [],
    Lex.TWord{_} <> M2.dens(toks)} : Lex.Lex}
  {==}

# one character of the span scanner and of the character machine, with its
# class and its control test named
law rel_hit:
  for +ch: Char
  for +tl: String
  for +cut: String
  for +nn: U32
  for md: Lex.Span
  for +toks: List<&2, Lex.Tok>
  for +lx: Lex.Lex
  for cls: Lex.Class
  for +ecls: {Lex.classify(ch) == cls : Lex.Class}
  for ctl: Bool
  for +ectl: {U32.is_lt(Char.to_u32(ch), 32) == ctl : Bool}
  for h_r: rel.go(cut, nn, md, toks, lx, SCon{ch, tl})
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  rel(Lex.tokens.hit(ch, tl, cut, nn, md, toks, cls, ctl), Lex.feed(ch, lx), tl)

def rel_hit(ch, tl, cut, nn, md, toks, lx, cls, ecls, ctl, ectl, h_r, h_s):
  match md cls ctl:
    case Lex.GIdle{} Lex.CPunct{pp} True{}:
      via(ch, lx, Lex.Idle{}, [], toks, Lex.CPunct{pp}, ecls, h_r)
    case Lex.GBad{} Lex.CPunct{pp} True{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.CPunct{pp}, ecls, h_r)
    case Lex.GWord{} Lex.CPunct{pp} True{}:
      (eq, more) = h_r
      (hd, hs) = more
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Idle{}, [],
        M2.den(pp) <> Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), []))} <> M2.dens(toks)},
          Lex.Lex{Lex.Idle{}, [], M2.den(pp) <> Lex.TWord{V.span.str(cut, nn, U32.is_zero(nn))} <> M2.dens(toks)},
              via(ch,
            lx, Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CPunct{pp}, ecls, eq),
          Equal.cong(String, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], M2.den(pp) <> Lex.TWord{xx} <> M2.dens(toks)},
            Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])), V.span.str(cut, nn, U32.is_zero(nn)),
              text_span(cut, nn, U32.is_zero(nn))))
    case Lex.GStr{} Lex.CPunct{pp} True{}:
      (eq, more) = h_r
      (hd, hs) = more
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), dlex(Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
        []), toks)), Lex.Lex{Lex.Bad{}, [], M2.dens(toks)},
          via(ch, lx, Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CPunct{pp}, ecls, eq),
          Equal.cong(Lex.Lex, Lex.Lex, xx => dlex(xx), Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []),
            toks), Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, True{}),
            str_as(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, True{}, ectl)))
    case Lex.GIdle{} Lex.CPunct{pp} False{}:
      via(ch, lx, Lex.Idle{}, [], toks, Lex.CPunct{pp}, ecls, h_r)
    case Lex.GBad{} Lex.CPunct{pp} False{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.CPunct{pp}, ecls, h_r)
    case Lex.GWord{} Lex.CPunct{pp} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Idle{}, [],
        M2.den(pp) <> Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), []))} <> M2.dens(toks)},
          Lex.Lex{Lex.Idle{}, [], M2.den(pp) <> Lex.TWord{V.span.str(cut, nn, U32.is_zero(nn))} <> M2.dens(toks)},
              via(ch,
            lx, Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CPunct{pp}, ecls, eq),
          Equal.cong(String, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], M2.den(pp) <> Lex.TWord{xx} <> M2.dens(toks)},
            Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])), V.span.str(cut, nn, U32.is_zero(nn)),
              text_span(cut, nn, U32.is_zero(nn))))
    case Lex.GStr{} Lex.CPunct{pp} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      grow_rel(ch, tl, cut, nn, toks, lx, Lex.Str{}, hd, hs,
          Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), dlex(Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
            []), toks)), dlex(Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{})),
            via(ch, lx, Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CPunct{pp}, ecls, eq),
            Equal.cong(Lex.Lex, Lex.Lex, xx => dlex(xx), Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
              []), toks), Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{}),
              str_as(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{}, ectl))))
    case Lex.GIdle{} Lex.CQuote{} True{}:
      (Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Str{}, [], M2.dens(toks)},
            Lex.Lex{Lex.Str{}, Lex.tokens.rev(tl, 0, True{}, []), M2.dens(toks)}, via(ch, lx, Lex.Idle{}, [], toks,
              Lex.CQuote{}, ecls, h_r),
            Equal.cong(List<&2, Char>, Lex.Lex, xx => Lex.Lex{Lex.Str{}, xx, M2.dens(toks)}, [], Lex.tokens.rev(tl, 0,
              True{}, []),
              Equal.sym(List<&2, Char>, Lex.tokens.rev(tl, 0, True{}, []), [], rev_zero(tl, 0, [])))),
          (sdrop_zero(tl, tl, {==}), short_tail(ch, tl, h_s)))
    case Lex.GBad{} Lex.CQuote{} True{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.CQuote{}, ecls, h_r)
    case Lex.GWord{} Lex.CQuote{} True{}:
      (eq, more) = h_r
      (hd, hs) = more
      (Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Str{}, [], Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn,
        U32.is_zero(nn), []))} <> M2.dens(toks)},
            Lex.Lex{Lex.Str{}, Lex.tokens.rev(tl, 0, True{}, []), Lex.TWord{V.span.str(cut, nn,
              U32.is_zero(nn))} <> M2.dens(toks)},
            Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Str{}, [],
              Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), []))} <> M2.dens(toks)},
              Lex.Lex{Lex.Str{}, [], Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn),
                []))} <> M2.dens(toks)}, via(ch, lx, Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks,
                  Lex.CQuote{}, ecls, eq), {==}),
            two_cong(tl, Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])), V.span.str(cut, nn,
              U32.is_zero(nn)), text_span(cut, nn, U32.is_zero(nn)), toks)),
          (sdrop_zero(tl, tl, {==}), short_tail(ch, tl, h_s)))
    case Lex.GStr{} Lex.CQuote{} True{}:
      Empty.absurd(rel(Lex.tokens.hit(ch, tl, cut, nn, Lex.GStr{}, toks, Lex.CQuote{}, True{}), Lex.feed(ch, lx),
        tl), not_ctl(ch, 34, cls_quote(ch, ecls), {==}, ectl))
    case Lex.GIdle{} Lex.CQuote{} False{}:
      (Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Str{}, [], M2.dens(toks)},
            Lex.Lex{Lex.Str{}, Lex.tokens.rev(tl, 0, True{}, []), M2.dens(toks)}, via(ch, lx, Lex.Idle{}, [], toks,
              Lex.CQuote{}, ecls, h_r),
            Equal.cong(List<&2, Char>, Lex.Lex, xx => Lex.Lex{Lex.Str{}, xx, M2.dens(toks)}, [], Lex.tokens.rev(tl, 0,
              True{}, []),
              Equal.sym(List<&2, Char>, Lex.tokens.rev(tl, 0, True{}, []), [], rev_zero(tl, 0, [])))),
          (sdrop_zero(tl, tl, {==}), short_tail(ch, tl, h_s)))
    case Lex.GBad{} Lex.CQuote{} False{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.CQuote{}, ecls, h_r)
    case Lex.GWord{} Lex.CQuote{} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      (Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Str{}, [], Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn,
        U32.is_zero(nn), []))} <> M2.dens(toks)},
            Lex.Lex{Lex.Str{}, Lex.tokens.rev(tl, 0, True{}, []), Lex.TWord{V.span.str(cut, nn,
              U32.is_zero(nn))} <> M2.dens(toks)},
            Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Str{}, [],
              Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), []))} <> M2.dens(toks)},
              Lex.Lex{Lex.Str{}, [], Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn),
                []))} <> M2.dens(toks)}, via(ch, lx, Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks,
                  Lex.CQuote{}, ecls, eq), {==}),
            two_cong(tl, Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])), V.span.str(cut, nn,
              U32.is_zero(nn)), text_span(cut, nn, U32.is_zero(nn)), toks)),
          (sdrop_zero(tl, tl, {==}), short_tail(ch, tl, h_s)))
    case Lex.GStr{} Lex.CQuote{} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Idle{}, [], Lex.TStr{Lex.text(Lex.tokens.rev(cut, nn,
        U32.is_zero(nn), []))} <> M2.dens(toks)},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{V.span.str(cut, nn, U32.is_zero(nn))} <> M2.dens(toks)}, via(ch, lx,
            Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CQuote{}, ecls, eq),
          Equal.cong(String, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TStr{xx} <> M2.dens(toks)},
            Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])), V.span.str(cut, nn, U32.is_zero(nn)),
              text_span(cut, nn, U32.is_zero(nn))))
    case Lex.GIdle{} Lex.CSpace{} True{}:
      via(ch, lx, Lex.Idle{}, [], toks, Lex.CSpace{}, ecls, h_r)
    case Lex.GBad{} Lex.CSpace{} True{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.CSpace{}, ecls, h_r)
    case Lex.GWord{} Lex.CSpace{} True{}:
      (eq, more) = h_r
      (hd, hs) = more
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Idle{}, [], Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn,
        U32.is_zero(nn), []))} <> M2.dens(toks)},
          Lex.Lex{Lex.Idle{}, [], Lex.TWord{V.span.str(cut, nn, U32.is_zero(nn))} <> M2.dens(toks)}, via(ch, lx,
            Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CSpace{}, ecls, eq),
          Equal.cong(String, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TWord{xx} <> M2.dens(toks)},
            Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])), V.span.str(cut, nn, U32.is_zero(nn)),
              text_span(cut, nn, U32.is_zero(nn))))
    case Lex.GStr{} Lex.CSpace{} True{}:
      (eq, more) = h_r
      (hd, hs) = more
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), dlex(Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
        []), toks)), Lex.Lex{Lex.Bad{}, [], M2.dens(toks)},
          via(ch, lx, Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CSpace{}, ecls, eq),
          Equal.cong(Lex.Lex, Lex.Lex, xx => dlex(xx), Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []),
            toks), Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, True{}),
            str_as(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, True{}, ectl)))
    case Lex.GIdle{} Lex.CSpace{} False{}:
      via(ch, lx, Lex.Idle{}, [], toks, Lex.CSpace{}, ecls, h_r)
    case Lex.GBad{} Lex.CSpace{} False{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.CSpace{}, ecls, h_r)
    case Lex.GWord{} Lex.CSpace{} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Idle{}, [], Lex.TWord{Lex.text(Lex.tokens.rev(cut, nn,
        U32.is_zero(nn), []))} <> M2.dens(toks)},
          Lex.Lex{Lex.Idle{}, [], Lex.TWord{V.span.str(cut, nn, U32.is_zero(nn))} <> M2.dens(toks)}, via(ch, lx,
            Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CSpace{}, ecls, eq),
          Equal.cong(String, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TWord{xx} <> M2.dens(toks)},
            Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])), V.span.str(cut, nn, U32.is_zero(nn)),
              text_span(cut, nn, U32.is_zero(nn))))
    case Lex.GStr{} Lex.CSpace{} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      grow_rel(ch, tl, cut, nn, toks, lx, Lex.Str{}, hd, hs,
          Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), dlex(Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
            []), toks)), dlex(Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{})),
            via(ch, lx, Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CSpace{}, ecls, eq),
            Equal.cong(Lex.Lex, Lex.Lex, xx => dlex(xx), Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
              []), toks), Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{}),
              str_as(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{}, ectl))))
    case Lex.GIdle{} Lex.CBack{} True{}:
      via(ch, lx, Lex.Idle{}, [], toks, Lex.CBack{}, ecls, h_r)
    case Lex.GBad{} Lex.CBack{} True{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.CBack{}, ecls, h_r)
    case Lex.GWord{} Lex.CBack{} True{}:
      (eq, more) = h_r
      (hd, hs) = more
      via(ch, lx, Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CBack{}, ecls, eq)
    case Lex.GStr{} Lex.CBack{} True{}:
      Empty.absurd(rel(Lex.tokens.hit(ch, tl, cut, nn, Lex.GStr{}, toks, Lex.CBack{}, True{}), Lex.feed(ch, lx), tl),
        not_ctl(ch, 92, cls_back(ch, ecls), {==}, ectl))
    case Lex.GIdle{} Lex.CBack{} False{}:
      via(ch, lx, Lex.Idle{}, [], toks, Lex.CBack{}, ecls, h_r)
    case Lex.GBad{} Lex.CBack{} False{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.CBack{}, ecls, h_r)
    case Lex.GWord{} Lex.CBack{} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      via(ch, lx, Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CBack{}, ecls, eq)
    case Lex.GStr{} Lex.CBack{} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      via(ch, lx, Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.CBack{}, ecls, eq)
    case Lex.GIdle{} Lex.COther{} True{}:
      (Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Word{}, [ch], M2.dens(toks)},
            Lex.Lex{Lex.Word{}, Lex.tokens.rev(tl, 0, True{}, [ch]), M2.dens(toks)}, via(ch, lx, Lex.Idle{}, [], toks,
              Lex.COther{}, ecls, h_r),
            Equal.cong(List<&2, Char>, Lex.Lex, xx => Lex.Lex{Lex.Word{}, xx, M2.dens(toks)}, [ch], Lex.tokens.rev(tl,
              0, True{}, [ch]),
              Equal.sym(List<&2, Char>, Lex.tokens.rev(tl, 0, True{}, [ch]), [ch], rev_zero(tl, 0, [ch])))),
          (sdrop_zero(tl, tl, {==}), h_s))
    case Lex.GBad{} Lex.COther{} True{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.COther{}, ecls, h_r)
    case Lex.GWord{} Lex.COther{} True{}:
      (eq, more) = h_r
      (hd, hs) = more
      grow_rel(ch, tl, cut, nn, toks, lx, Lex.Word{}, hd, hs, via(ch, lx, Lex.Word{}, Lex.tokens.rev(cut, nn,
        U32.is_zero(nn), []), toks, Lex.COther{}, ecls, eq))
    case Lex.GStr{} Lex.COther{} True{}:
      (eq, more) = h_r
      (hd, hs) = more
      Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), dlex(Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
        []), toks)), Lex.Lex{Lex.Bad{}, [], M2.dens(toks)},
          via(ch, lx, Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.COther{}, ecls, eq),
          Equal.cong(Lex.Lex, Lex.Lex, xx => dlex(xx), Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []),
            toks), Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, True{}),
            str_as(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, True{}, ectl)))
    case Lex.GIdle{} Lex.COther{} False{}:
      (Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), Lex.Lex{Lex.Word{}, [ch], M2.dens(toks)},
            Lex.Lex{Lex.Word{}, Lex.tokens.rev(tl, 0, True{}, [ch]), M2.dens(toks)}, via(ch, lx, Lex.Idle{}, [], toks,
              Lex.COther{}, ecls, h_r),
            Equal.cong(List<&2, Char>, Lex.Lex, xx => Lex.Lex{Lex.Word{}, xx, M2.dens(toks)}, [ch], Lex.tokens.rev(tl,
              0, True{}, [ch]),
              Equal.sym(List<&2, Char>, Lex.tokens.rev(tl, 0, True{}, [ch]), [ch], rev_zero(tl, 0, [ch])))),
          (sdrop_zero(tl, tl, {==}), h_s))
    case Lex.GBad{} Lex.COther{} False{}:
      via(ch, lx, Lex.Bad{}, [], toks, Lex.COther{}, ecls, h_r)
    case Lex.GWord{} Lex.COther{} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      grow_rel(ch, tl, cut, nn, toks, lx, Lex.Word{}, hd, hs, via(ch, lx, Lex.Word{}, Lex.tokens.rev(cut, nn,
        U32.is_zero(nn), []), toks, Lex.COther{}, ecls, eq))
    case Lex.GStr{} Lex.COther{} False{}:
      (eq, more) = h_r
      (hd, hs) = more
      grow_rel(ch, tl, cut, nn, toks, lx, Lex.Str{}, hd, hs,
          Equal.trans(Lex.Lex, dlex(Lex.feed(ch, lx)), dlex(Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
            []), toks)), dlex(Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{})),
            via(ch, lx, Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, Lex.COther{}, ecls, eq),
            Equal.cong(Lex.Lex, Lex.Lex, xx => dlex(xx), Lex.step.str(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn),
              []), toks), Lex.step.str.go(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{}),
              str_as(ch, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), toks, False{}, ectl))))

# one character keeps a scanner state and a lexer state related
law rel_step:
  for +sc: Lex.Scan
  for +lx: Lex.Lex
  for +ch: Char
  for +tl: String
  for h_r: rel(sc, lx, SCon{ch, tl})
  for h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  rel(Lex.tokens.feed(ch, tl, sc), Lex.feed(ch, lx), tl)

def rel_step(sc, lx, ch, tl, h_r, h_s):
  match sc:
    case Lex.Old{ol}:
      dlex_feed(ch, lx, ol, h_r)
    case Lex.Go{cut, nn, md, toks}:
      rel_hit(ch, tl, cut, nn, md, toks, lx, Lex.classify(ch), {==}, U32.is_lt(Char.to_u32(ch), 32), {==}, h_r, h_s)

# the tokens at the end of a word, with spans replaced: the word's span as text
law end_word:
  for +cut: String
  for +nn: U32
  for +toks: List<&2, Lex.Tok>
  {M2.dens(Lex.tokens.done(cut, nn, Lex.GWord{}, toks))
    == Lex.finish(Lex.Lex{Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), M2.dens(toks)}) : List<&2, Lex.Tok>}

def end_word(cut, nn, toks):
  dr = dens_rev(Lex.TWordS{cut, nn} <> toks, [])
  ts = Equal.sym(String, Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])), V.span.str(cut, nn, U32.is_zero(nn)),
    text_span(cut, nn, U32.is_zero(nn)))
  %ts : {M2.dens(Lex.tokens.done(cut, nn, Lex.GWord{}, toks))
    == List.reverse(&2, Lex.Tok, Lex.TWord{_} <> M2.dens(toks)) : List<&2, Lex.Tok>}
  dr

# rel_end, once the scanner's tokens are known to be finish of a lexer state
# the same as lx up to spans
law rel_end.at:
  for -tks: List<&2, Lex.Tok>
  for -ls: Lex.Lex
  for +lx: Lex.Lex
  for et: {M2.dens(tks) == Lex.finish(ls) : List<&2, Lex.Tok>}
  for hl: {dlex(lx) == ls : Lex.Lex}
  {M2.dens(tks) == M2.dens(Lex.finish(lx)) : List<&2, Lex.Tok>}

def rel_end.at(tks, ls, lx, et, hl):
  Equal.trans(List<&2, Lex.Tok>, M2.dens(tks), Lex.finish(dlex(lx)), M2.dens(Lex.finish(lx)),
    Equal.trans(List<&2, Lex.Tok>, M2.dens(tks), Lex.finish(ls), Lex.finish(dlex(lx)), et,
      Equal.cong(Lex.Lex, List<&2, Lex.Tok>, xx => Lex.finish(xx), ls, dlex(lx), Equal.sym(Lex.Lex, dlex(lx), ls, hl))),
    Equal.sym(List<&2, Lex.Tok>, M2.dens(Lex.finish(lx)), Lex.finish(dlex(lx)), dens_finish(lx)))

# at the end of the text, a scanner state and a lexer state give the same
# tokens up to spans
law rel_end:
  for sc: Lex.Scan
  for +lx: Lex.Lex
  for h_r: rel(sc, lx, "")
  {M2.dens(Lex.tokens.end(sc)) == M2.dens(Lex.finish(lx)) : List<&2, Lex.Tok>}

def rel_end(sc, lx, h_r):
  match sc:
    case Lex.Old{ol}:
      Equal.trans(List<&2, Lex.Tok>, M2.dens(Lex.finish(ol)), Lex.finish(dlex(lx)), M2.dens(Lex.finish(lx)),
        Equal.trans(List<&2, Lex.Tok>, M2.dens(Lex.finish(ol)), Lex.finish(dlex(ol)), Lex.finish(dlex(lx)),
          dens_finish(ol),
          Equal.cong(Lex.Lex, List<&2, Lex.Tok>, xx => Lex.finish(xx), dlex(ol), dlex(lx), Equal.sym(Lex.Lex,
            dlex(lx), dlex(ol), h_r))),
        Equal.sym(List<&2, Lex.Tok>, M2.dens(Lex.finish(lx)), Lex.finish(dlex(lx)), dens_finish(lx)))
    case Lex.Go{cut, nn, Lex.GIdle{}, toks}:
      rel_end.at(Lex.tokens.done(cut, nn, Lex.GIdle{}, toks), Lex.Lex{Lex.Idle{}, [], M2.dens(toks)}, lx,
        dens_rev(toks, []), h_r)
    case Lex.Go{cut, nn, Lex.GWord{}, toks}:
      (eq, _more) = h_r
      rel_end.at(Lex.tokens.done(cut, nn, Lex.GWord{}, toks),
        Lex.Lex{Lex.Word{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), M2.dens(toks)}, lx, end_word(cut, nn, toks),
            eq)
    case Lex.Go{cut, nn, Lex.GStr{}, toks}:
      (eq, _more) = h_r
      rel_end.at(Lex.tokens.done(cut, nn, Lex.GStr{}, toks),
        Lex.Lex{Lex.Str{}, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), M2.dens(toks)}, lx,
          dens_rev(Lex.TBad{} <> toks, []), eq)
    case Lex.Go{cut, nn, Lex.GBad{}, toks}:
      rel_end.at(Lex.tokens.done(cut, nn, Lex.GBad{}, toks), Lex.Lex{Lex.Bad{}, [], M2.dens(toks)}, lx,
        dens_rev(Lex.TBad{} <> toks, []), h_r)

# the span scanner and the character machine, run over the rest of a short
# text from related states, give the same tokens up to spans
law lex_agree_go:
  for +ss: String
  for +sc: Lex.Scan
  for +lx: Lex.Lex
  for h_r: rel(sc, lx, ss)
  for +h_s: {D1.short(ss) == True{} : Bool}
  {M2.dens(Lex.tokens.go(ss, sc)) == M2.dens(Lex.finish(Lex.run(String.to_list(ss), lx))) : List<&2, Lex.Tok>}

def lex_agree_go(ss, sc, lx, h_r, h_s):
  match ss:
    case SNil{}:
      rel_end(sc, lx, h_r)
    case SCon{ch, tl}:
      lex_agree_go(tl, Lex.tokens.feed(ch, tl, sc), Lex.feed(ch, lx), rel_step(sc, lx, ch, tl, h_r, h_s),
        short_tail(ch, tl, h_s))

# WP-L1: for a text of at most 2^32 - 1 characters, the lexer's span path
# and its character path give the same tokens, once spans are replaced by the
# characters they cover
law lexers_agree:
  for +ss: String
  for h_s: {D1.short(ss) == True{} : Bool}
  {M2.dens(Lex.tokens(ss)) == M2.dens(Lex.finish(Lex.run(String.to_list(ss), Lex.Lex{Lex.Idle{}, [], []}))) : List<&2,
    Lex.Tok>}

def lexers_agree(ss, h_s):
  lex_agree_go(ss, Lex.Go{"", 0, Lex.GIdle{}, []}, Lex.Lex{Lex.Idle{}, [], []}, {==}, h_s)

# whether a list is empty
def tnil(xs: List<&2, Lex.Tok>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case _:
      False{}

# the first token of a list, or a bad one
def thead(xs: List<&2, Lex.Tok>) -> Lex.Tok:
  match xs:
    case Nil{}:
      Lex.TBad{}
    case hd <> _:
      hd

# the tokens after the first
def ttail(xs: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match xs:
    case Nil{}:
      Nil{}
    case _ <> tl:
      tl
