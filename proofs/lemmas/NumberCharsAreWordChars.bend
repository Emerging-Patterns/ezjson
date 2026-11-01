# every character of a JSON number is a word character
import Base
import ../../src/value.bend as V
import ../../src/lex.bend as Lex
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ../../laws/defs/Digit.bend as D2
import ./ArrayLength.bend as M1
import ./LexemeOrder.bend as M2
import ./WellFormedCells.bend as M3
import ./WordLexing.bend as M4

# a digit is a word character
law oth_digit:
  for +ch: Char
  for h: {D2.digit(ch) == True{} : Bool}
  {Lex.classify(ch) == Lex.COther{} : Lex.Class}

def oth_digit(ch, h):
  M4.cls_by(ch, xx => V.num.ok.digit(xx), h, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# digit1-9 is a word character
law oth_digit19:
  for +ch: Char
  for h: {D1.digit19(ch) == True{} : Bool}
  {Lex.classify(ch) == Lex.COther{} : Lex.Class}

def oth_digit19(ch, h):
  M4.cls_by(ch, xx => V.num.ok.lead(xx), h, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a character that is one given word code point is a word character
law oth_cp:
  for +ch: Char
  for kk: U32
  for h: {D1.is_cp(ch, kk) == True{} : Bool}
  for hk: {Lex.classify.go(kk) == Lex.COther{} : Lex.Class}
  {Lex.classify(ch) == Lex.COther{} : Lex.Class}

def oth_cp(ch, kk, h, hk):
  match ch:
    case Chr{+uu}:
      eu = Equal.sym(U32, uu, kk, M3.ueq(uu, kk, h))
      %eu : {Lex.classify.go(_) == Lex.COther{} : Lex.Class}
      hk

# an e or E is a word character
law oth_e:
  for +ch: Char
  for h: {D1.is_e(ch) == True{} : Bool}
  {Lex.classify(ch) == Lex.COther{} : Lex.Class}

def oth_e(ch, h):
  M4.cls_by(ch, xx => V.num.ok.expmark(xx), h, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a true `when`, by its condition
law when_el:
  for cc: Bool
  for +yy: Bool
  for +nn: Bool
  for pp: Type
  for h: {D1.when(cc, yy, nn) == True{} : Bool}
  for kt: {cc == True{} : Bool} -> {yy == True{} : Bool} -> pp
  for kf: {nn == True{} : Bool} -> pp
  pp

def when_el(cc, _yy, _nn, _pp, h, kt, kf):
  match cc:
    case True{}:
      kt({==}, h)
    case False{}:
      kf(h)

# *DIGIT: word characters
law oth_digits_end:
  for +cs: List<&2, Char>
  for h: {D1.digits_end(cs) == True{} : Bool}
  M4.others(cs)

def oth_digits_end(cs, h):
  match cs:
    case Nil{}:
      Unit{}
    case Con{+hd, +tl}:
      when_el(D2.digit(hd), D1.digits_end(tl), False{}, M4.others(hd <> tl), h,
        ed => et => (oth_digit(hd, ed), oth_digits_end(tl, et)), ef => M2.no(M4.others(hd <> tl), ef))

# 1*DIGIT: word characters
law oth_digits1_end:
  for +cs: List<&2, Char>
  for h: {D1.digits1_end(cs) == True{} : Bool}
  M4.others(cs)

def oth_digits1_end(cs, h):
  match cs:
    case Nil{}:
      M2.no(M4.others([]), h)
    case Con{+hd, +tl}:
      when_el(D2.digit(hd), D1.digits_end(tl), False{}, M4.others(hd <> tl), h,
        ed => et => (oth_digit(hd, ed), oth_digits_end(tl, et)), ef => M2.no(M4.others(hd <> tl), ef))

# an exponent's body: word characters
law oth_exp_body:
  for +cs: List<&2, Char>
  for h: {D1.exp_body(cs) == True{} : Bool}
  M4.others(cs)

def oth_exp_body(cs, h):
  match cs:
    case Nil{}:
      M2.no(M4.others([]), h)
    case Con{+hd, +tl}:
      when_el(D1.is_cp(hd, 43), D1.digits1_end(tl), D1.when(D1.is_cp(hd, 45), D1.digits1_end(tl),
        D1.when(D2.digit(hd), D1.digits_end(tl), False{})), M4.others(hd <> tl), h,
        ec => et => (oth_cp(hd, 43, ec, {==}), oth_digits1_end(tl, et)),
        h2 => when_el(D1.is_cp(hd, 45), D1.digits1_end(tl), D1.when(D2.digit(hd), D1.digits_end(tl),
          False{}), M4.others(hd <> tl), h2,
          ec => et => (oth_cp(hd, 45, ec, {==}), oth_digits1_end(tl, et)),
          h3 => when_el(D2.digit(hd), D1.digits_end(tl), False{}, M4.others(hd <> tl), h3,
            ed => et => (oth_digit(hd, ed), oth_digits_end(tl, et)), ef => M2.no(M4.others(hd <> tl), ef))))

# frac's other digits, then an exponent: word characters
law oth_digits_exp_end:
  for +cs: List<&2, Char>
  for h: {D1.digits_exp_end(cs) == True{} : Bool}
  M4.others(cs)

def oth_digits_exp_end(cs, h):
  match cs:
    case Nil{}:
      Unit{}
    case Con{+hd, +tl}:
      when_el(D2.digit(hd), D1.digits_exp_end(tl), D1.when(D1.is_e(hd), D1.exp_body(tl), False{}),
        M4.others(hd <> tl), h,
        ed => et => (oth_digit(hd, ed), oth_digits_exp_end(tl, et)),
        h2 => when_el(D1.is_e(hd), D1.exp_body(tl), False{}, M4.others(hd <> tl), h2,
          ee => et => (oth_e(hd, ee), oth_exp_body(tl, et)), ef => M2.no(M4.others(hd <> tl), ef)))

# frac's body: word characters
law oth_frac_body:
  for +cs: List<&2, Char>
  for h: {D1.frac_body(cs) == True{} : Bool}
  M4.others(cs)

def oth_frac_body(cs, h):
  match cs:
    case Nil{}:
      M2.no(M4.others([]), h)
    case Con{+hd, +tl}:
      when_el(D2.digit(hd), D1.digits_exp_end(tl), False{}, M4.others(hd <> tl), h,
        ed => et => (oth_digit(hd, ed), oth_digits_exp_end(tl, et)), ef => M2.no(M4.others(hd <> tl), ef))

# after an int of 0: word characters
law oth_zero_rest:
  for +cs: List<&2, Char>
  for h: {D1.zero_rest(cs) == True{} : Bool}
  M4.others(cs)

def oth_zero_rest(cs, h):
  match cs:
    case Nil{}:
      Unit{}
    case Con{+hd, +tl}:
      when_el(D2.digit(hd), False{}, D1.when(D1.is_cp(hd, 46), D1.frac_body(tl), D1.when(D1.is_e(hd),
        D1.exp_body(tl), False{})), M4.others(hd <> tl), h,
        _ed => ef => M2.no(M4.others(hd <> tl), ef),
        h2 => when_el(D1.is_cp(hd, 46), D1.frac_body(tl), D1.when(D1.is_e(hd), D1.exp_body(tl), False{}),
          M4.others(hd <> tl), h2,
          ec => et => (oth_cp(hd, 46, ec, {==}), oth_frac_body(tl, et)),
          h3 => when_el(D1.is_e(hd), D1.exp_body(tl), False{}, M4.others(hd <> tl), h3,
            ee => et => (oth_e(hd, ee), oth_exp_body(tl, et)), ef => M2.no(M4.others(hd <> tl), ef))))

# after digit1-9: word characters
law oth_digits_rest:
  for +cs: List<&2, Char>
  for h: {D1.digits_rest(cs) == True{} : Bool}
  M4.others(cs)

def oth_digits_rest(cs, h):
  match cs:
    case Nil{}:
      Unit{}
    case Con{+hd, +tl}:
      when_el(D2.digit(hd), D1.digits_rest(tl), D1.when(D1.is_cp(hd, 46), D1.frac_body(tl),
        D1.when(D1.is_e(hd), D1.exp_body(tl), False{})), M4.others(hd <> tl), h,
        ed => et => (oth_digit(hd, ed), oth_digits_rest(tl, et)),
        h2 => when_el(D1.is_cp(hd, 46), D1.frac_body(tl), D1.when(D1.is_e(hd), D1.exp_body(tl), False{}),
          M4.others(hd <> tl), h2,
          ec => et => (oth_cp(hd, 46, ec, {==}), oth_frac_body(tl, et)),
          h3 => when_el(D1.is_e(hd), D1.exp_body(tl), False{}, M4.others(hd <> tl), h3,
            ee => et => (oth_e(hd, ee), oth_exp_body(tl, et)), ef => M2.no(M4.others(hd <> tl), ef))))

# int, then frac and exp: word characters
law oth_int_end:
  for +cs: List<&2, Char>
  for h: {D1.int_end(cs) == True{} : Bool}
  M4.others(cs)

def oth_int_end(cs, h):
  match cs:
    case Nil{}:
      M2.no(M4.others([]), h)
    case Con{+hd, +tl}:
      when_el(D1.is_cp(hd, 48), D1.zero_rest(tl), D1.when(D1.digit19(hd), D1.digits_rest(tl), False{}),
        M4.others(hd <> tl),
        h,
        ec => et => (oth_cp(hd, 48, ec, {==}), oth_zero_rest(tl, et)),
        h2 => when_el(D1.digit19(hd), D1.digits_rest(tl), False{}, M4.others(hd <> tl), h2,
          ed => et => (oth_digit19(hd, ed), oth_digits_rest(tl, et)), ef => M2.no(M4.others(hd <> tl), ef)))

# a JSON number: word characters
law oth_number:
  for +cs: List<&2, Char>
  for h: {D1.number(cs) == True{} : Bool}
  M4.others(cs)

def oth_number(cs, h):
  match cs:
    case Nil{}:
      M2.no(M4.others([]), h)
    case Con{+hd, +tl}:
      when_el(D1.is_cp(hd, 45), D1.int_end(tl), D1.int_end(hd <> tl), M4.others(hd <> tl), h,
        ec => et => (oth_cp(hd, 45, ec, {==}), oth_int_end(tl, et)),
        ei => oth_int_end(hd <> tl, ei))

# str_eq_sound, once the first characters' comparison is named: String.eq
# walks the rests with String.order.go, carrying that comparison
law str_eq_at:
  for cc: Cmp
  for +xx: U32
  for +yy: U32
  for +t1: String
  for +t2: String
  for ec: {U32.cmp(xx, yy) == cc : Cmp}
  for h: {Cmp.is_eq(String.order.go(t1, t2, cc)) == True{} : Bool}
  for ih: {String.eq(t1, t2) == True{} : Bool} -> {t1 == t2 : String}
  {SCon{Chr{xx}, t1} == SCon{Chr{yy}, t2} : String}

def str_eq_at(cc, xx, yy, t1, t2, ec, h, ih):
  match cc:
    case LT{}:
      Empty.absurd({SCon{Chr{xx}, t1} == SCon{Chr{yy}, t2} : String},
        M2.false_true(Equal.trans(Bool, False{}, Cmp.is_eq(String.order.go(t1, t2, LT{})), True{},
          Equal.sym(Bool, Cmp.is_eq(String.order.go(t1, t2, LT{})), False{}, M1.order_go_ne_eq(t1, t2, LT{}, {==})),
              h)))
    case GT{}:
      Empty.absurd({SCon{Chr{xx}, t1} == SCon{Chr{yy}, t2} : String},
        M2.false_true(Equal.trans(Bool, False{}, Cmp.is_eq(String.order.go(t1, t2, GT{})), True{},
          Equal.sym(Bool, Cmp.is_eq(String.order.go(t1, t2, GT{})), False{}, M1.order_go_ne_eq(t1, t2, GT{}, {==})),
              h)))
    case EQ{}:
      et = ih(h)
      ex = M3.ueq(xx, yy, Equal.cong(Cmp, Bool, zz => Cmp.is_eq(zz), U32.cmp(xx, yy), EQ{}, ec))
      %ex : {SCon{Chr{xx}, t1} == SCon{Chr{_}, t2} : String}
      %et : {SCon{Chr{xx}, t1} == SCon{Chr{xx}, _} : String}
      {==}

# strings String.eq calls equal are equal
law str_eq_sound:
  for +aa: String
  for +bb: String
  for h: {String.eq(aa, bb) == True{} : Bool}
  {aa == bb : String}

def str_eq_sound(aa, bb, h):
  match aa bb:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h2, t2}:
      Empty.absurd({SNil{} == SCon{h2, t2} : String}, M2.false_true(h))
    case SCon{h1, t1} SNil{}:
      Empty.absurd({SCon{h1, t1} == SNil{} : String}, M2.false_true(h))
    case SCon{Chr{+xx}, +t1} SCon{Chr{+yy}, +t2}:
      str_eq_at(U32.cmp(xx, yy), xx, yy, t1, t2, {==}, h, hh => str_eq_sound(t1, t2, hh))
