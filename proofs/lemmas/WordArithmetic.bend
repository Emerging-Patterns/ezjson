# U32 subtraction by zero, and indexing the cells arr builds
import Base
import ../../src/value.bend as V
import ../../src/lazy.bend as Lazy
import ../../laws/AtIndexesArrays.bend as L1
import ../../laws/defs/ArrayAccess.bend as D1
import ../../laws/defs/CursorAndNumberRules.bend as D2
import ./ArrayLength.bend as M1
import ./WellFormedCells.bend as M2

# one bit of adc_zero_carry, the rest given
law adc_zero_carry.at:
  for +qq: Nat
  for ab: Bool
  for -at: Word(qq)
  for ih: {Word.adc(qq, at, Word.zero(qq), True{}, True{}) == at : Word(qq)}
  {Word.adc.con(qq, at, Word.zero(qq), True{}, Bool.full_add(ab, True{}, True{})) == WCon{ab, at} : Word.Con<qq>}

def adc_zero_carry.at(qq, ab, at, ih):
  match ab:
    case True{}:
      Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{True{}, ww},
        Word.adc(qq, at, Word.zero(qq), True{}, True{}), at, ih)
    case False{}:
      Equal.cong(Word(qq), Word.Con<qq>, ww => WCon{False{}, ww},
        Word.adc(qq, at, Word.zero(qq), True{}, True{}), at, ih)

# subtracting zero with the carry in adds nothing: a - 0 - 1 + 1 is a
law adc_zero_carry:
  for +pp: Nat
  for +aw: Word(pp)
  {Word.adc(pp, aw, Word.zero(pp), True{}, True{}) == aw : Word(pp)}

def adc_zero_carry(pp, aw):
  match pp:
    case 0n:
      match aw:
        case WNil{}:
          {==}
    case 1n+(+qq):
      match aw:
        case WCon{ab, +at}:
          adc_zero_carry.at(qq, ab, at, adc_zero_carry(qq, at))

# a word whose first bit is clear and that is not zero: the rest is not zero
law fin_ff:
  for cc: Cmp
  for h_nz: {Cmp.is_eq(Word.cmp.fin(False{}, False{}, cc)) == False{} : Bool}
  {Cmp.is_eq(cc) == False{} : Bool}

def fin_ff(cc, h_nz):
  match cc:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, M1.true_false(h_nz))
    case GT{}:
      {==}

# subtracting zero with no carry in takes one: a - 0 - 1, one less than a
# when a is not zero
law adc_zero_borrow:
  for +pp: Nat
  for +aw: Word(pp)
  for h_nz: {Cmp.is_eq(Word.cmp(pp, aw, Word.zero(pp))) == False{} : Bool}
  {1n+Word.to_nat(pp, Word.adc(pp, aw, Word.zero(pp), True{}, False{})) == Word.to_nat(pp, aw) : Nat}

def adc_zero_borrow(pp, aw, h_nz):
  match pp:
    case 0n:
      match aw:
        case WNil{}:
          Empty.absurd({1n == 0n : Nat}, M1.true_false(h_nz))
    case 1n+(+qq):
      match aw:
        case WCon{True{}, +at}:
          lc = Equal.sym(Word(qq), Word.adc(qq, at, Word.zero(qq), True{}, True{}), at, adc_zero_carry(qq, at))
          %lc : {1n+Nat.double(Word.to_nat(qq, _)) == 1n+Nat.double(Word.to_nat(qq, at)) : Nat}
          {==}
        case WCon{False{}, +at}:
          ih = adc_zero_borrow(qq, at, fin_ff(Word.cmp(qq, at, Word.zero(qq)), h_nz))
          %ih : {2n+Nat.double(Word.to_nat(qq, Word.adc(qq, at, Word.zero(qq), True{}, False{})))
            == Nat.double(_) : Nat}
          {==}

# one less than a nonzero U32, as a Nat
law u32_dec:
  for +uu: U32
  for h_nz: {U32.is_zero(uu) == False{} : Bool}
  {U32.to_nat(uu) == 1n+U32.to_nat(U32.sub(uu, 1)) : Nat}

def u32_dec(uu, h_nz):
  match uu:
    case U32{WCon{True{}, +at}}:
      lc = Equal.sym(Word(31n), Word.adc(31n, at, Word.zero(31n), True{}, True{}), at, adc_zero_carry(31n, at))
      %lc : {1n+Nat.double(Word.to_nat(31n, at)) == 1n+Nat.double(Word.to_nat(31n, _)) : Nat}
      {==}
    case U32{WCon{False{}, +at}}:
      ih = adc_zero_borrow(31n, at, fin_ff(Word.cmp(31n, at, Word.zero(31n)), h_nz))
      %ih : {Nat.double(_)
        == 2n+Nat.double(Word.to_nat(31n, Word.adc(31n, at, Word.zero(31n), True{}, False{}))) : Nat}
      {==}

# one cell of at.go, once whether the index is zero is known
law at_step:
  for +hd: V.Json
  for +tl: List<&2, V.Json>
  for +idx: U32
  for bz: Bool
  for ez: {U32.is_zero(idx) == bz : Bool}
  for ih: {V.at.go(V.arr.go(tl), U32.sub(idx, 1)) == D1.nth(tl, U32.to_nat(U32.sub(idx, 1))) : V.Json}
  {Lazy.stop(V.Json, bz, hd, _u => V.at.go(V.arr.go(tl), U32.sub(idx, 1)))
    == D1.nth(hd <> tl, U32.to_nat(idx)) : V.Json}

def at_step(hd, tl, idx, bz, ez, ih):
  match bz:
    case True{}:
      e0 = Equal.sym(U32, idx, 0, M2.ueq(idx, 0, ez))
      %e0 : {hd == D1.nth(hd <> tl, U32.to_nat(_)) : V.Json}
      {==}
    case False{}:
      en = Equal.sym(Nat, U32.to_nat(idx), 1n+U32.to_nat(U32.sub(idx, 1)), u32_dec(idx, ez))
      %en : {V.at.go(V.arr.go(tl), U32.sub(idx, 1)) == D1.nth(hd <> tl, _) : V.Json}
      ih

# at.go over the cells arr.go builds is nth at the index
law at_go_nth:
  for +xs: List<&2, V.Json>
  for +idx: U32
  {V.at.go(V.arr.go(xs), idx) == D1.nth(xs, U32.to_nat(idx)) : V.Json}

def at_go_nth(xs, idx):
  match xs:
    case Nil{}:
      {==}
    case hd <> tl:
      at_step(hd, tl, idx, U32.is_zero(idx), {==}, at_go_nth(tl, U32.sub(idx, 1)))

def L1.at_arr(xs, idx):
  at_go_nth(xs, idx)

# span.str of no characters, whatever the count
law span_take.nil:
  for +nn: U32
  for bz: Bool
  {V.span.str(SNil{}, nn, bz) == D2.take(SNil{}, U32.to_nat(nn)) : String}

def span_take.nil(_nn, bz):
  match bz:
    case True{}:
      {==}
    case False{}:
      {==}

# span.str of a character and the rest, once the zero test's answer is named
law span_take.cons:
  for +hd: Char
  for +tl: String
  for +nn: U32
  for bz: Bool
  for ez: {U32.is_zero(nn) == bz : Bool}
  for ih: {V.span.str(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)))
    == D2.take(tl, U32.to_nat(U32.sub(nn, 1))) : String}
  {V.span.str(SCon{hd, tl}, nn, bz) == D2.take(SCon{hd, tl}, U32.to_nat(nn)) : String}

def span_take.cons(hd, tl, nn, bz, ez, ih):
  match bz:
    case True{}:
      e0 = Equal.sym(U32, nn, 0, M2.ueq(nn, 0, ez))
      %e0 : {V.span.str(SCon{hd, tl}, nn, True{}) == D2.take(SCon{hd, tl}, U32.to_nat(_)) : String}
      {==}
    case False{}:
      en = Equal.sym(Nat, U32.to_nat(nn), 1n+U32.to_nat(U32.sub(nn, 1)), u32_dec(nn, ez))
      %en : {SCon{hd, V.span.str(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)))}
        == D2.take(SCon{hd, tl}, _) : String}
      Equal.cong(String, String, xx => SCon{hd, xx}, V.span.str(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1))),
        D2.take(tl, U32.to_nat(U32.sub(nn, 1))), ih)

# a span's characters are the first nn characters of its source
law span_take:
  for +src: String
  for +nn: U32
  {V.span.str(src, nn, U32.is_zero(nn)) == D2.take(src, U32.to_nat(nn)) : String}

def span_take(src, nn):
  match src:
    case SNil{}:
      span_take.nil(nn, U32.is_zero(nn))
    case SCon{hd, tl}:
      span_take.cons(hd, tl, nn, U32.is_zero(nn), {==}, span_take(tl, U32.sub(nn, 1)))

# laws/SkipPassesOneValue.bend: skip, one event of the reader at a time

# a count, if there is one
def ms(xx: Maybe<&2, Nat>) -> Bool:
  match xx:
    case Some{_}:
      True{}
    case None{}:
      False{}

# a count of exactly one
def m1(xx: Maybe<&2, Nat>) -> Bool:
  match xx:
    case Some{kk}:
      match kk:
        case 0n:
          False{}
        case 1n+jj:
          match jj:
            case 0n:
              True{}
            case 1n+_:
              False{}
    case None{}:
      False{}
