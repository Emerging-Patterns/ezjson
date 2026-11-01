# the digits of int and frac, character by character
import Base
import ../../src/value.bend as V
import ../../laws/NumOkIsNumberRule.bend as L1
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ../../laws/defs/Digit.bend as D2
import ./ArrayLength.bend as M1
import ./LexemeOrder.bend as M2
import ./NumOkStates.bend as M3
import ./WellFormedCells.bend as M4

# exp's last digits: *DIGIT, then the end
law st_expd:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NExpD{}) == D1.digits_end(cs) : Bool}

# one digit test of an exponent, the rest given
law expd_at:
  for +tl: List<&2, Char>
  for bd: Bool
  for ih: {V.num.ok.go(tl, V.NExpD{}) == D1.digits_end(tl) : Bool}
  {V.num.ok.go(tl, V.num.ok.step.expd.go(bd)) == D1.when(bd, D1.digits_end(tl), False{}) : Bool}

def expd_at(tl, bd, ih):
  match bd:
    case True{}:
      ih
    case False{}:
      M3.st_bad(tl)

def st_expd(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      expd_at(tl, D2.digit(ch), st_expd(tl))

# exp after its sign: 1*DIGIT, then the end
law st_expn:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NExpN{}) == D1.digits1_end(cs) : Bool}

def st_expn(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      expd_at(tl, D2.digit(ch), st_expd(tl))

# after e, not a plus: a minus, or the first digit
law exp_minus_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bm: Bool
  {V.num.ok.go(tl, V.num.ok.step.exps.minus.go(Char.to_u32(ch), bm))
    == D1.when(bm, D1.digits1_end(tl), D1.when(D2.digit(ch), D1.digits_end(tl), False{})) : Bool}

def exp_minus_at(ch, tl, bm):
  match bm:
    case True{}:
      st_expn(tl)
    case False{}:
      expd_at(tl, D2.digit(ch), st_expd(tl))

# after e: a plus, a minus, or the first digit
law exp_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bp: Bool
  {V.num.ok.go(tl, V.num.ok.step.exps.go(Char.to_u32(ch), bp))
    == D1.when(bp, D1.digits1_end(tl),
      D1.when(D1.is_cp(ch, 45), D1.digits1_end(tl),
        D1.when(D2.digit(ch), D1.digits_end(tl), False{}))) : Bool}

def exp_at(ch, tl, bp):
  match bp:
    case True{}:
      st_expn(tl)
    case False{}:
      exp_minus_at(ch, tl, D1.is_cp(ch, 45))

# exp after its e
law st_exp:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NExp{}) == D1.exp_body(cs) : Bool}

def st_exp(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      exp_at(ch, tl, D1.is_cp(ch, 43))

# an e starts exp; anything else is not a number
law mark_at:
  for +tl: List<&2, Char>
  for be: Bool
  {V.num.ok.go(tl, V.num.ok.step.mark.go(be)) == D1.when(be, D1.exp_body(tl), False{}) : Bool}

def mark_at(tl, be):
  match be:
    case True{}:
      st_exp(tl)
    case False{}:
      M3.st_bad(tl)

# frac's digits after the first, then [ exp ], then the end
law st_frac:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NFrac{}) == D1.digits_exp_end(cs) : Bool}

# one character of frac's digits, the rest given
law frac_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bd: Bool
  for ih: {V.num.ok.go(tl, V.NFrac{}) == D1.digits_exp_end(tl) : Bool}
  {V.num.ok.go(tl, V.num.ok.step.frac.go(Char.to_u32(ch), True{}, bd))
    == D1.when(bd, D1.digits_exp_end(tl), D1.when(D1.is_e(ch), D1.exp_body(tl), False{})) : Bool}

def frac_at(ch, tl, bd, ih):
  match bd:
    case True{}:
      ih
    case False{}:
      mark_at(tl, D1.is_e(ch))

def st_frac(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      frac_at(ch, tl, D2.digit(ch), st_frac(tl))

# frac after its decimal point
law st_dot:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NDot{}) == D1.frac_body(cs) : Bool}

# the first digit of frac
law dot_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bd: Bool
  {V.num.ok.go(tl, V.num.ok.step.frac.go(Char.to_u32(ch), False{}, bd))
    == D1.when(bd, D1.digits_exp_end(tl), False{}) : Bool}

def dot_at(_ch, tl, bd):
  match bd:
    case True{}:
      st_frac(tl)
    case False{}:
      M3.st_bad(tl)

def st_dot(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      dot_at(ch, tl, D2.digit(ch))

# after int, not a digit: a decimal point, an e, or not a number
law other_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bdot: Bool
  {V.num.ok.go(tl, V.num.ok.step.body.other.go(Char.to_u32(ch), bdot))
    == D1.when(bdot, D1.frac_body(tl), D1.when(D1.is_e(ch), D1.exp_body(tl), False{})) : Bool}

def other_at(ch, tl, bdot):
  match bdot:
    case True{}:
      st_dot(tl)
    case False{}:
      mark_at(tl, D1.is_e(ch))

# after an int of 0
law st_zero:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NZero{}) == D1.zero_rest(cs) : Bool}

# one character after 0: a digit is not a number
law zero_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bd: Bool
  {V.num.ok.go(tl, V.num.ok.step.body.go(Char.to_u32(ch), False{}, bd))
    == D1.when(bd, False{},
      D1.when(D1.is_cp(ch, 46), D1.frac_body(tl), D1.when(D1.is_e(ch), D1.exp_body(tl), False{}))) : Bool}

def zero_at(ch, tl, bd):
  match bd:
    case True{}:
      M3.st_bad(tl)
    case False{}:
      other_at(ch, tl, D1.is_cp(ch, 46))

def st_zero(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      zero_at(ch, tl, D2.digit(ch))

# after digit1-9 and any digits
law st_dig:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NDig{}) == D1.digits_rest(cs) : Bool}

# one character after int's digits, the rest given
law dig_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bd: Bool
  for ih: {V.num.ok.go(tl, V.NDig{}) == D1.digits_rest(tl) : Bool}
  {V.num.ok.go(tl, V.num.ok.step.body.go(Char.to_u32(ch), True{}, bd))
    == D1.when(bd, D1.digits_rest(tl),
      D1.when(D1.is_cp(ch, 46), D1.frac_body(tl), D1.when(D1.is_e(ch), D1.exp_body(tl), False{}))) : Bool}

def dig_at(ch, tl, bd, ih):
  match bd:
    case True{}:
      ih
    case False{}:
      other_at(ch, tl, D1.is_cp(ch, 46))

def st_dig(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      dig_at(ch, tl, D2.digit(ch), st_dig(tl))

# int's first character, not 0: digit1-9 or not a number
law lead_at:
  for +tl: List<&2, Char>
  for bl: Bool
  {V.num.ok.go(tl, V.num.ok.step.lead(bl)) == D1.when(bl, D1.digits_rest(tl), False{}) : Bool}

def lead_at(tl, bl):
  match bl:
    case True{}:
      st_dig(tl)
    case False{}:
      M3.st_bad(tl)

# int's first character
law int_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bz: Bool
  {V.num.ok.go(tl, V.num.ok.step.int.go(Char.to_u32(ch), bz))
    == D1.when(bz, D1.zero_rest(tl), D1.when(D1.digit19(ch), D1.digits_rest(tl), False{})) : Bool}

def int_at(ch, tl, bz):
  match bz:
    case True{}:
      st_zero(tl)
    case False{}:
      lead_at(tl, D1.digit19(ch))

# int [ frac ] [ exp ]
law st_int:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NInt{}) == D1.int_end(cs) : Bool}

def st_int(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      int_at(ch, tl, D1.is_cp(ch, 48))

# the first character: minus, or int's first
law start_at:
  for +ch: Char
  for +tl: List<&2, Char>
  for bm: Bool
  {V.num.ok.go(tl, V.num.ok.step.start.go(Char.to_u32(ch), bm))
    == D1.when(bm, D1.int_end(tl), D1.int_end(ch <> tl)) : Bool}

def start_at(ch, tl, bm):
  match bm:
    case True{}:
      st_int(tl)
    case False{}:
      st_int(ch <> tl)

# the whole number
law st_start:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NStart{}) == D1.number(cs) : Bool}

def st_start(cs):
  match cs:
    case Nil{}:
      {==}
    case ch <> tl:
      start_at(ch, tl, D1.is_cp(ch, 45))

def L1.num_grammar(txt):
  st_start(String.to_list(txt))

# a code point 48, `0`, is a digit
law c48.at:
  for bv: Bool
  for +cc: Char
  for e: {D1.is_cp(cc, 48) == bv : Bool}
  for hd: {D2.digit(cc) == False{} : Bool}
  {D1.is_cp(cc, 48) == False{} : Bool}

def c48.at(bv, cc, e, hd):
  match bv:
    case False{}:
      e
    case True{}:
      Empty.absurd({D1.is_cp(cc, 48) == False{} : Bool}, M1.true_false(Equal.trans(Bool, True{},
        Bool.and(U32.is_ge(Char.to_u32(cc), 48), U32.is_le(Char.to_u32(cc), 57)), False{},
        Equal.cong(U32, Bool, zz => Bool.and(U32.is_ge(zz, 48), U32.is_le(zz, 57)), 48, Char.to_u32(cc),
          Equal.sym(U32, Char.to_u32(cc), 48, M4.ueq(Char.to_u32(cc), 48, e))), hd)))

law c48:
  for +cc: Char
  for hd: {D2.digit(cc) == False{} : Bool}
  {D1.is_cp(cc, 48) == False{} : Bool}

def c48(cc, hd):
  c48.at(D1.is_cp(cc, 48), cc, {==}, hd)

# a word at least 49 is at least 48: the two differ in the lowest bit
law ge_bit:
  for kk: Cmp
  for bv: Bool
  for h: {Cmp.is_ge(Word.cmp.fin(bv, True{}, kk)) == True{} : Bool}
  {Cmp.is_ge(Word.cmp.fin(bv, False{}, kk)) == True{} : Bool}

def ge_bit(kk, bv, h):
  match kk:
    case LT{}:
      M2.no({Cmp.is_ge(Word.cmp.fin(bv, False{}, LT{})) == True{} : Bool}, h)
    case EQ{}:
      match bv:
        case True{}:
          {==}
        case False{}:
          M2.no({Cmp.is_ge(Word.cmp.fin(False{}, False{}, EQ{})) == True{} : Bool}, h)
    case GT{}:
      {==}

# the tail of a code point's bits
def u_tl(uu: U32) -> Word(31n):
  match uu:
    case U32{WCon{_, tt}}:
      tt

# digit1-9 is a digit
law d19:
  for +cc: Char
  for +h: {D1.digit19(cc) == True{} : Bool}
  {D2.digit(cc) == True{} : Bool}

def d19(cc, h):
  match cc:
    case Chr{U32{WCon{+bv, +tt}}}:
      M2.and2(U32.is_ge(U32{WCon{bv, tt}}, 48), U32.is_le(U32{WCon{bv, tt}}, 57), ge_bit(Word.cmp(31n, tt, u_tl(49)),
          bv,
        M2.and_left(U32.is_ge(U32{WCon{bv, tt}}, 49), U32.is_le(U32{WCon{bv, tt}}, 57), h)),
        M2.and_right(U32.is_ge(U32{WCon{bv, tt}}, 49), U32.is_le(U32{WCon{bv, tt}}, 57), h))
