# proofs of laws/AsU32ReadsPlainDigits.bend
import Base
import ../src/value.bend as V
import ../laws/AsU32ReadsPlainDigits.bend as Laws
import ../laws/NumOkIsNumberRule.bend as L1
import ../laws/defs/CursorAndNumberRules.bend as D1
import ../laws/defs/Digit.bend as D2
import ./lemmas/ArrayLength.bend as M1
import ./lemmas/LexemeOrder.bend as M2
import ./lemmas/NatArithmetic.bend as M3
import ./lemmas/NumberDigits.bend as M4
import ./lemmas/WellFormedCells.bend as M5

# multiplication distributes over a sum on the left
law nat_mul_add_r:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  {Nat.mul(Nat.add(aa, bb), cc) == Nat.add(Nat.mul(aa, cc), Nat.mul(bb, cc)) : Nat}

def nat_mul_add_r(aa, bb, cc):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.trans(Nat, Nat.add(cc, Nat.mul(Nat.add(pp, bb), cc)),
        Nat.add(cc, Nat.add(Nat.mul(pp, cc), Nat.mul(bb, cc))),
        Nat.add(Nat.add(cc, Nat.mul(pp, cc)), Nat.mul(bb, cc)),
        Equal.cong(Nat, Nat, xx => Nat.add(cc, xx), Nat.mul(Nat.add(pp, bb), cc),
          Nat.add(Nat.mul(pp, cc), Nat.mul(bb, cc)), nat_mul_add_r(pp, bb, cc)),
        Equal.sym(Nat, Nat.add(Nat.add(cc, Nat.mul(pp, cc)), Nat.mul(bb, cc)),
          Nat.add(cc, Nat.add(Nat.mul(pp, cc), Nat.mul(bb, cc))), M3.nat_add_assoc(cc, Nat.mul(pp, cc), Nat.mul(bb,
              cc))))

# multiplication distributes over a sum on the right
law nat_mul_add_l:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  {Nat.mul(aa, Nat.add(bb, cc)) == Nat.add(Nat.mul(aa, bb), Nat.mul(aa, cc)) : Nat}

def nat_mul_add_l(aa, bb, cc):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.trans(Nat, Nat.add(Nat.add(bb, cc), Nat.mul(pp, Nat.add(bb, cc))),
        Nat.add(Nat.add(bb, cc), Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc))), Nat.add(Nat.add(bb, Nat.mul(pp, bb)),
          Nat.add(cc, Nat.mul(pp, cc))),
        Equal.cong(Nat, Nat, xx => Nat.add(Nat.add(bb, cc), xx), Nat.mul(pp, Nat.add(bb, cc)),
          Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc)), nat_mul_add_l(pp, bb, cc)),
        Equal.trans(Nat, Nat.add(Nat.add(bb, cc), Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc))), Nat.add(Nat.mul(pp, bb),
          Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc))), Nat.add(Nat.add(bb, Nat.mul(pp, bb)), Nat.add(cc, Nat.mul(pp,
          cc))), Equal.trans(Nat, Nat.add(Nat.add(bb, cc), Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc))),
          Nat.add(Nat.add(bb, cc), Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc))), Nat.add(Nat.mul(pp, bb),
          Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc))), Equal.cong(Nat, Nat, z1 => Nat.add(z1, Nat.add(Nat.mul(pp, bb),
          Nat.mul(pp, cc))), Nat.add(bb, cc), Nat.add(bb, cc), {==}), Equal.trans(Nat, Nat.add(Nat.add(bb, cc),
          Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc))), Nat.add(Nat.add(bb, cc), Nat.add(Nat.mul(pp, bb), Nat.mul(pp,
          cc))), Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc))), Equal.cong(Nat, Nat,
          z2 => Nat.add(Nat.add(bb, cc), z2), Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc)), Nat.add(Nat.mul(pp, bb),
          Nat.mul(pp, cc)), {==}), Equal.trans(Nat, Nat.add(Nat.add(bb, cc), Nat.add(Nat.mul(pp, bb), Nat.mul(pp,
          cc))), Nat.add(bb, Nat.add(cc, Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc)))), Nat.add(Nat.mul(pp, bb),
          Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc))), M3.nat_add_assoc(bb, cc, Nat.add(Nat.mul(pp, bb), Nat.mul(pp,
              cc))),
          Equal.trans(Nat, Nat.add(bb, Nat.add(cc, Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc)))), Nat.add(bb,
          Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc), cc))), Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc),
          Nat.add(bb, cc))), Equal.cong(Nat, Nat, z4 => Nat.add(bb, z4), Nat.add(cc, Nat.add(Nat.mul(pp, bb),
          Nat.mul(pp, cc))), Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc), cc)), Equal.trans(Nat, Nat.add(cc,
          Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc))), Nat.add(Nat.mul(pp, bb), Nat.add(cc, Nat.mul(pp, cc))),
          Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc), cc)), M3.nat_add_lcomm(cc, Nat.mul(pp, bb), Nat.mul(pp,
              cc)),
          Equal.cong(Nat, Nat, z3 => Nat.add(Nat.mul(pp, bb), z3), Nat.add(cc, Nat.mul(pp, cc)), Nat.add(Nat.mul(pp,
          cc), cc), M3.nat_add_comm(cc, Nat.mul(pp, cc))))), Equal.trans(Nat, Nat.add(bb, Nat.add(Nat.mul(pp, bb),
          Nat.add(Nat.mul(pp, cc), cc))), Nat.add(Nat.mul(pp, bb), Nat.add(bb, Nat.add(Nat.mul(pp, cc), cc))),
          Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc))), M3.nat_add_lcomm(bb, Nat.mul(pp, bb),
          Nat.add(Nat.mul(pp, cc), cc)), Equal.cong(Nat, Nat, z5 => Nat.add(Nat.mul(pp, bb), z5), Nat.add(bb,
          Nat.add(Nat.mul(pp, cc), cc)), Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc)), M3.nat_add_lcomm(bb, Nat.mul(pp,
              cc),
          cc))))))), Equal.sym(Nat, Nat.add(Nat.add(bb, Nat.mul(pp, bb)), Nat.add(cc, Nat.mul(pp, cc))),
          Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc))), Equal.trans(Nat, Nat.add(Nat.add(bb,
          Nat.mul(pp, bb)), Nat.add(cc, Nat.mul(pp, cc))), Nat.add(Nat.add(Nat.mul(pp, bb), bb), Nat.add(cc,
          Nat.mul(pp, cc))), Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc))), Equal.cong(Nat, Nat,
          z6 => Nat.add(z6, Nat.add(cc, Nat.mul(pp, cc))), Nat.add(bb, Nat.mul(pp, bb)), Nat.add(Nat.mul(pp, bb), bb),
          M3.nat_add_comm(bb, Nat.mul(pp, bb))), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(pp, bb), bb), Nat.add(cc,
          Nat.mul(pp, cc))), Nat.add(Nat.add(Nat.mul(pp, bb), bb), Nat.add(Nat.mul(pp, cc), cc)), Nat.add(Nat.mul(pp,
          bb), Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc))), Equal.cong(Nat, Nat, z7 => Nat.add(Nat.add(Nat.mul(pp, bb),
          bb), z7), Nat.add(cc, Nat.mul(pp, cc)), Nat.add(Nat.mul(pp, cc), cc), M3.nat_add_comm(cc, Nat.mul(pp, cc))),
          Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(pp, bb), bb), Nat.add(Nat.mul(pp, cc), cc)), Nat.add(Nat.mul(pp,
          bb), Nat.add(bb, Nat.add(Nat.mul(pp, cc), cc))), Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc),
          Nat.add(bb, cc))), M3.nat_add_assoc(Nat.mul(pp, bb), bb, Nat.add(Nat.mul(pp, cc), cc)), Equal.cong(Nat, Nat,
          z8 => Nat.add(Nat.mul(pp, bb), z8), Nat.add(bb, Nat.add(Nat.mul(pp, cc), cc)), Nat.add(Nat.mul(pp, cc),
          Nat.add(bb, cc)), M3.nat_add_lcomm(bb, Nat.mul(pp, cc), cc))))))))

# twice a on the left
law nat_mul_double_l:
  for +aa: Nat
  for +bb: Nat
  {Nat.mul(Nat.double(aa), bb) == Nat.double(Nat.mul(aa, bb)) : Nat}

def nat_mul_double_l(aa, bb):
  Equal.trans(Nat, Nat.mul(Nat.double(aa), bb), Nat.mul(Nat.add(aa, aa), bb), Nat.double(Nat.mul(aa, bb)),
    Equal.cong(Nat, Nat, xx => Nat.mul(xx, bb), Nat.double(aa), Nat.add(aa, aa), M3.nat_double(aa)),
    Equal.trans(Nat, Nat.mul(Nat.add(aa, aa), bb), Nat.add(Nat.mul(aa, bb), Nat.mul(aa, bb)),
      Nat.double(Nat.mul(aa, bb)), nat_mul_add_r(aa, aa, bb),
      Equal.sym(Nat, Nat.double(Nat.mul(aa, bb)), Nat.add(Nat.mul(aa, bb), Nat.mul(aa, bb)),
        M3.nat_double(Nat.mul(aa, bb)))))

# twice b on the right
law nat_mul_double_r:
  for +aa: Nat
  for +bb: Nat
  {Nat.mul(aa, Nat.double(bb)) == Nat.double(Nat.mul(aa, bb)) : Nat}

def nat_mul_double_r(aa, bb):
  Equal.trans(Nat, Nat.mul(aa, Nat.double(bb)), Nat.mul(aa, Nat.add(bb, bb)), Nat.double(Nat.mul(aa, bb)),
    Equal.cong(Nat, Nat, xx => Nat.mul(aa, xx), Nat.double(bb), Nat.add(bb, bb), M3.nat_double(bb)),
    Equal.trans(Nat, Nat.mul(aa, Nat.add(bb, bb)), Nat.add(Nat.mul(aa, bb), Nat.mul(aa, bb)),
      Nat.double(Nat.mul(aa, bb)), nat_mul_add_l(aa, bb, bb),
      Equal.sym(Nat, Nat.double(Nat.mul(aa, bb)), Nat.add(Nat.mul(aa, bb), Nat.mul(aa, bb)),
        M3.nat_double(Nat.mul(aa, bb)))))

# multiplication associates
law nat_mul_assoc:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  {Nat.mul(Nat.mul(aa, bb), cc) == Nat.mul(aa, Nat.mul(bb, cc)) : Nat}

def nat_mul_assoc(aa, bb, cc):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.trans(Nat, Nat.mul(Nat.add(bb, Nat.mul(pp, bb)), cc),
        Nat.add(Nat.mul(bb, cc), Nat.mul(Nat.mul(pp, bb), cc)), Nat.add(Nat.mul(bb, cc), Nat.mul(pp, Nat.mul(bb, cc))),
        nat_mul_add_r(bb, Nat.mul(pp, bb), cc),
        Equal.cong(Nat, Nat, xx => Nat.add(Nat.mul(bb, cc), xx), Nat.mul(Nat.mul(pp, bb), cc),
          Nat.mul(pp, Nat.mul(bb, cc)), nat_mul_assoc(pp, bb, cc)))

# 1 times a
law nat_mul_one:
  for +aa: Nat
  {Nat.mul(aa, 1n) == aa : Nat}

def nat_mul_one(aa):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.mul(pp, 1n), pp, nat_mul_one(pp))

# a Nat compares equal to itself
law nat_cmp_refl:
  for +aa: Nat
  {Nat.cmp(aa, aa) == EQ{} : Cmp}

def nat_cmp_refl(aa):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      nat_cmp_refl(pp)

# nothing is below 0
law nat_nlt_zero:
  for +aa: Nat
  {Nat.is_lt(aa, 0n) == False{} : Bool}

def nat_nlt_zero(aa):
  match aa:
    case 0n:
      {==}
    case 1n+_pp:
      {==}

# a sum is never below its left addend
law nat_nlt_add:
  for +aa: Nat
  for +bb: Nat
  {Nat.is_lt(Nat.add(aa, bb), aa) == False{} : Bool}

def nat_nlt_add(aa, bb):
  match aa:
    case 0n:
      nat_nlt_zero(bb)
    case 1n+(+pp):
      nat_nlt_add(pp, bb)

# a sum whose left addend is not below c is not below c
law nat_ge_add:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  for h: {Nat.is_lt(aa, cc) == False{} : Bool}
  {Nat.is_lt(Nat.add(aa, bb), cc) == False{} : Bool}

def nat_ge_add(aa, bb, cc, h):
  match aa cc:
    case 0n 0n:
      nat_nlt_zero(bb)
    case 0n 1n+_cp:
      Empty.absurd({Nat.is_lt(bb, cc) == False{} : Bool}, M1.true_false(h))
    case 1n+_ap 0n:
      {==}
    case 1n+(+ap) 1n+(+cp):
      nat_ge_add(ap, bb, cp, h)

# below c is below c + 1
law nat_lt_succ:
  for +aa: Nat
  for +cc: Nat
  for h: {Nat.is_lt(aa, cc) == True{} : Bool}
  {Nat.is_lt(aa, 1n+cc) == True{} : Bool}

def nat_lt_succ(aa, cc, h):
  match aa cc:
    case 0n 0n:
      {==}
    case 0n 1n+_cp:
      {==}
    case 1n+_ap 0n:
      Empty.absurd({Nat.is_lt(aa, 1n) == True{} : Bool}, M2.false_true(h))
    case 1n+(+ap) 1n+(+cp):
      nat_lt_succ(ap, cp, h)

# below c, the right addend of a sum below c is below c too
law nat_lt_add_l:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  for h: {Nat.is_lt(Nat.add(aa, bb), cc) == True{} : Bool}
  {Nat.is_lt(bb, cc) == True{} : Bool}

def nat_lt_add_l(aa, bb, cc, h):
  match aa:
    case 0n:
      h
    case 1n+(+ap):
      match cc:
        case 0n:
          Empty.absurd({Nat.is_lt(bb, 0n) == True{} : Bool}, M2.false_true(h))
        case 1n+(+cp):
          nat_lt_succ(bb, cp, nat_lt_add_l(ap, bb, cp, h))

# the witness of a >= b: a is b and a - b
law nat_ge_ex:
  for +aa: Nat
  for +bb: Nat
  for h: {Nat.is_lt(aa, bb) == False{} : Bool}
  {Nat.add(bb, Nat.sub(aa, bb)) == aa : Nat}

def nat_ge_ex(aa, bb, h):
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+_bp:
      Empty.absurd({Nat.add(bb, Nat.sub(0n, bb)) == 0n : Nat}, M1.true_false(h))
    case 1n+_ap 0n:
      {==}
    case 1n+(+ap) 1n+(+bp):
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(bp, Nat.sub(ap, bp)), ap, nat_ge_ex(ap, bp, h))

# a + 1 + z is never a
law nat_add_ne:
  for +aa: Nat
  for +zz: Nat
  for h: {Nat.add(aa, 1n+zz) == aa : Nat}
  Empty

def nat_add_ne(aa, zz, h):
  match aa:
    case 0n:
      M2.false_true(Equal.cong(Nat, Bool, xx => Nat.is_eq(xx, 0n), 1n+zz, 0n, h))
    case 1n+(+ap):
      nat_add_ne(ap, zz, Equal.cong(Nat, Nat, xx => M3.npred(xx), 1n+Nat.add(ap, 1n+zz), 1n+ap, h))

# a sum a + (c + y) is below c only when false
law nat_nlt_add2:
  for +aa: Nat
  for +cc: Nat
  for +yy: Nat
  {Nat.is_lt(Nat.add(aa, Nat.add(cc, yy)), cc) == False{} : Bool}

def nat_nlt_add2(aa, cc, yy):
  lc = Equal.sym(Nat, Nat.add(aa, Nat.add(cc, yy)), Nat.add(cc, Nat.add(aa, yy)), M3.nat_add_lcomm(aa, cc, yy))
  %lc : {Nat.is_lt(_, cc) == False{} : Bool}
  nat_nlt_add(cc, Nat.add(aa, yy))

# s + k*t is e and e is below t: k is 0, and s is e
law nat_mod_small:
  for +kk: Nat
  for +ss: Nat
  for +ee: Nat
  for +tt: Nat
  for h: {Nat.add(ss, Nat.mul(kk, tt)) == ee : Nat}
  for he: {Nat.is_lt(ee, tt) == True{} : Bool}
  {ss == ee : Nat}

def nat_mod_small(kk, ss, ee, tt, h, he):
  match kk:
    case 0n:
      Equal.trans(Nat, ss, Nat.add(ss, 0n), ee, Equal.sym(Nat, Nat.add(ss, 0n), ss, M3.nat_add_zero(ss)), h)
    case 1n+(+kp):
      Empty.absurd({ss == ee : Nat},
        M1.true_false(Equal.trans(Bool, True{}, Nat.is_lt(ee, tt), False{},
          Equal.sym(Bool, Nat.is_lt(ee, tt), True{}, he),
          Equal.trans(Bool, Nat.is_lt(ee, tt), Nat.is_lt(Nat.add(ss, Nat.add(tt, Nat.mul(kp, tt))), tt), False{},
            Equal.cong(Nat, Bool, xx => Nat.is_lt(xx, tt), ee, Nat.add(ss, Nat.add(tt, Nat.mul(kp, tt))),
              Equal.sym(Nat, Nat.add(ss, Nat.add(tt, Nat.mul(kp, tt))), ee, h)),
            nat_nlt_add2(ss, tt, Nat.mul(kp, tt))))))

# laws/AsU32ReadsPlainDigits.bend: words as Nats

# a bit as a Nat
def bit_nat(bb: Bool) -> Nat:
  match bb:
    case False{}:
      0n
    case True{}:
      1n

# a word one bit wider, as a Nat: its low bit and twice the rest
law w_nat_con:
  for pp: Nat
  for bb: Bool
  for ww: Word(pp)
  {Word.to_nat(1n+pp, WCon{bb, ww}) == Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, ww))) : Nat}

def w_nat_con(_pp, bb, _ww):
  match bb:
    case False{}:
      {==}
    case True{}:
      {==}

# comparing a bit and twice a Nat: the rest decides, the bit breaks a tie
law nat_cmp_bits:
  for +aa: Nat
  for +bb: Nat
  for xx: Bool
  for yy: Bool
  {Nat.cmp(Nat.add(bit_nat(xx), Nat.double(aa)), Nat.add(bit_nat(yy), Nat.double(bb))) ==
    Word.cmp.fin(xx, yy, Nat.cmp(aa, bb)) : Cmp}

def nat_cmp_bits(aa, bb, xx, yy):
  match aa bb:
    case 0n 0n:
      match xx yy:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+(+ap) 0n:
      match xx yy:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 0n 1n+(+bp):
      match xx yy:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+(+ap) 1n+(+bp):
      match xx yy:
        case False{} False{}:
          nat_cmp_bits(ap, bp, False{}, False{})
        case False{} True{}:
          nat_cmp_bits(ap, bp, False{}, True{})
        case True{} False{}:
          nat_cmp_bits(ap, bp, True{}, False{})
        case True{} True{}:
          nat_cmp_bits(ap, bp, True{}, True{})

# words compare as the Nats they are
law w_cmp:
  for +nn: Nat
  for aa: Word(nn)
  for bb: Word(nn)
  {Word.cmp(nn, aa, bb) == Nat.cmp(Word.to_nat(nn, aa), Word.to_nat(nn, bb)) : Cmp}

def w_cmp(nn, aa, bb):
  match nn:
    case 0n:
      match aa bb:
        case WNil{} WNil{}:
          {==}
    case 1n+(+pp):
      match aa bb:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(False{}, False{}, Word.cmp(pp, at, bt)), Word.cmp.fin(False{}, False{},
            Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
            Nat.cmp(Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(False{}),
              Nat.double(Word.to_nat(pp, bt)))),
            Equal.cong(Cmp, Cmp, zz => Word.cmp.fin(False{}, False{}, zz), Word.cmp(pp, at, bt),
              Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt)),
              w_cmp(pp, at, bt)),
            Equal.sym(Cmp, Nat.cmp(Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, at))),
              Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, bt)))),
              Word.cmp.fin(False{}, False{}, Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
                nat_cmp_bits(Word.to_nat(pp, at), Word.to_nat(pp, bt), False{}, False{})))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(False{}, True{}, Word.cmp(pp, at, bt)), Word.cmp.fin(False{}, True{},
            Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
            Nat.cmp(Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(True{}),
              Nat.double(Word.to_nat(pp, bt)))),
            Equal.cong(Cmp, Cmp, zz => Word.cmp.fin(False{}, True{}, zz), Word.cmp(pp, at, bt), Nat.cmp(Word.to_nat(pp,
              at), Word.to_nat(pp, bt)),
              w_cmp(pp, at, bt)),
            Equal.sym(Cmp, Nat.cmp(Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(True{}),
              Nat.double(Word.to_nat(pp, bt)))),
              Word.cmp.fin(False{}, True{}, Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
                nat_cmp_bits(Word.to_nat(pp, at), Word.to_nat(pp, bt), False{}, True{})))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(True{}, False{}, Word.cmp(pp, at, bt)), Word.cmp.fin(True{}, False{},
            Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
            Nat.cmp(Nat.add(bit_nat(True{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(False{}),
              Nat.double(Word.to_nat(pp, bt)))),
            Equal.cong(Cmp, Cmp, zz => Word.cmp.fin(True{}, False{}, zz), Word.cmp(pp, at, bt), Nat.cmp(Word.to_nat(pp,
              at), Word.to_nat(pp, bt)),
              w_cmp(pp, at, bt)),
            Equal.sym(Cmp, Nat.cmp(Nat.add(bit_nat(True{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(False{}),
              Nat.double(Word.to_nat(pp, bt)))),
              Word.cmp.fin(True{}, False{}, Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
                nat_cmp_bits(Word.to_nat(pp, at), Word.to_nat(pp, bt), True{}, False{})))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(True{}, True{}, Word.cmp(pp, at, bt)), Word.cmp.fin(True{}, True{},
            Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
            Nat.cmp(Nat.add(bit_nat(True{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(True{}),
              Nat.double(Word.to_nat(pp, bt)))),
            Equal.cong(Cmp, Cmp, zz => Word.cmp.fin(True{}, True{}, zz), Word.cmp(pp, at, bt), Nat.cmp(Word.to_nat(pp,
              at), Word.to_nat(pp, bt)),
              w_cmp(pp, at, bt)),
            Equal.sym(Cmp, Nat.cmp(Nat.add(bit_nat(True{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(True{}),
              Nat.double(Word.to_nat(pp, bt)))),
              Word.cmp.fin(True{}, True{}, Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
                nat_cmp_bits(Word.to_nat(pp, at), Word.to_nat(pp, bt), True{}, True{})))

# U32s compare as the Nats they are
law u_cmp:
  for aa: U32
  for bb: U32
  {U32.cmp(aa, bb) == Nat.cmp(U32.to_nat(aa), U32.to_nat(bb)) : Cmp}

def u_cmp(aa, bb):
  match aa bb:
    case U32{xw} U32{yw}:
      w_cmp(32n, xw, yw)

# a word, its complement and one make 2^nn
law w_not:
  for +nn: Nat
  for ww: Word(nn)
  {Nat.add(Word.to_nat(nn, Word.not(nn, ww)), Nat.add(Word.to_nat(nn, ww), 1n)) == M3.pow2(nn) : Nat}

def w_not(nn, ww):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match ww:
        case WCon{False{}, +tt}:
          Equal.trans(Nat, 1n+Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), Nat.add(Nat.double(Word.to_nat(pp,
            tt)), 1n)), Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), 1n+Nat.add(Nat.double(Word.to_nat(pp,
            tt)), 1n)), Nat.double(M3.pow2(pp)), Equal.sym(Nat, Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))),
            1n+Nat.add(Nat.double(Word.to_nat(pp, tt)), 1n)), 1n+Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))),
            Nat.add(Nat.double(Word.to_nat(pp, tt)), 1n)), M3.nat_add_succ(Nat.double(Word.to_nat(pp, Word.not(pp,
                tt))),
            Nat.add(Nat.double(Word.to_nat(pp, tt)), 1n))), Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(pp,
            Word.not(pp, tt))), 1n+Nat.add(Nat.double(Word.to_nat(pp, tt)), 1n)), Nat.add(Nat.double(Word.to_nat(pp,
            Word.not(pp, tt))), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n)), Nat.double(M3.pow2(pp)), Equal.cong(Nat,
            Nat, z9 => Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), z9),
            1n+Nat.add(Nat.double(Word.to_nat(pp, tt)), 1n), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n),
            Equal.sym(Nat, Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n), 1n+Nat.add(Nat.double(Word.to_nat(pp, tt)),
            1n), M3.nat_add_succ(Nat.double(Word.to_nat(pp, tt)), 1n))), Equal.trans(Nat,
            Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n)),
            Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), Nat.double(Nat.add(Word.to_nat(pp, tt), 1n))),
            Nat.double(M3.pow2(pp)), Equal.cong(Nat, Nat, z10 => Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))),
            z10), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n), Nat.double(Nat.add(Word.to_nat(pp, tt), 1n)),
            Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(pp, tt), 1n)), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n),
            M3.nat_double_add(Word.to_nat(pp, tt), 1n))), Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(pp,
                Word.not(pp,
            tt))), Nat.double(Nat.add(Word.to_nat(pp, tt), 1n))), Nat.double(Nat.add(Word.to_nat(pp, Word.not(pp, tt)),
            Nat.add(Word.to_nat(pp, tt), 1n))), Nat.double(M3.pow2(pp)), Equal.sym(Nat,
                Nat.double(Nat.add(Word.to_nat(pp,
            Word.not(pp, tt)), Nat.add(Word.to_nat(pp, tt), 1n))), Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp,
            tt))), Nat.double(Nat.add(Word.to_nat(pp, tt), 1n))), M3.nat_double_add(Word.to_nat(pp, Word.not(pp, tt)),
            Nat.add(Word.to_nat(pp, tt), 1n))), Equal.cong(Nat, Nat, z11 => Nat.double(z11), Nat.add(Word.to_nat(pp,
            Word.not(pp, tt)), Nat.add(Word.to_nat(pp, tt), 1n)), M3.pow2(pp), w_not(pp, tt))))))
        case WCon{True{}, +tt}:
          Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), 1n+Nat.add(Nat.double(Word.to_nat(pp,
            tt)), 1n)), Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), Nat.add(Nat.double(Word.to_nat(pp, tt)),
            2n)), Nat.double(M3.pow2(pp)), Equal.cong(Nat, Nat, z9 => Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp,
            tt))), z9), 1n+Nat.add(Nat.double(Word.to_nat(pp, tt)), 1n), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n),
            Equal.sym(Nat, Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n), 1n+Nat.add(Nat.double(Word.to_nat(pp, tt)),
            1n), M3.nat_add_succ(Nat.double(Word.to_nat(pp, tt)), 1n))), Equal.trans(Nat,
            Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n)),
            Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), Nat.double(Nat.add(Word.to_nat(pp, tt), 1n))),
            Nat.double(M3.pow2(pp)), Equal.cong(Nat, Nat, z10 => Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))),
            z10), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n), Nat.double(Nat.add(Word.to_nat(pp, tt), 1n)),
            Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(pp, tt), 1n)), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n),
            M3.nat_double_add(Word.to_nat(pp, tt), 1n))), Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(pp,
                Word.not(pp,
            tt))), Nat.double(Nat.add(Word.to_nat(pp, tt), 1n))), Nat.double(Nat.add(Word.to_nat(pp, Word.not(pp, tt)),
            Nat.add(Word.to_nat(pp, tt), 1n))), Nat.double(M3.pow2(pp)), Equal.sym(Nat,
                Nat.double(Nat.add(Word.to_nat(pp,
            Word.not(pp, tt)), Nat.add(Word.to_nat(pp, tt), 1n))), Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp,
            tt))), Nat.double(Nat.add(Word.to_nat(pp, tt), 1n))), M3.nat_double_add(Word.to_nat(pp, Word.not(pp, tt)),
            Nat.add(Word.to_nat(pp, tt), 1n))), Equal.cong(Nat, Nat, z11 => Nat.double(z11), Nat.add(Word.to_nat(pp,
            Word.not(pp, tt)), Nat.add(Word.to_nat(pp, tt), 1n)), M3.pow2(pp), w_not(pp, tt)))))

# w_not, with 2^nn named through uu
law w_not_u:
  for +nn: Nat
  for uu: Unit
  for ww: Word(nn)
  {Nat.add(Word.to_nat(nn, Word.not(nn, ww)), Nat.add(Word.to_nat(nn, ww), 1n)) == M3.pow2u(nn, uu) : Nat}

def w_not_u(nn, uu, ww):
  match uu:
    case Unit{}:
      w_not(nn, ww)

# laws/AsU32ReadsPlainDigits.bend: word addition as Nat addition

# the sum bit of a full add
def fa_s(sk: Bool & Bool) -> Bool:
  (ss, _kk) = sk
  ss

# the carry bit of a full add
def fa_k(sk: Bool & Bool) -> Bool:
  (_ss, kk) = sk
  kk

# the word adc adds: b, or its complement when ff
def adc_sel(nn: Nat, ww: Word(nn), ff: Bool) -> Word(nn):
  match ff:
    case False{}:
      ww
    case True{}:
      Word.not(nn, ww)

# how many times 2^nn adc's sum passes: its carry out
def adc_k(nn: Nat, aa: Word(nn), bb: Word(nn), ff: Bool, cc: Bool) -> Nat:
  match nn:
    case 0n:
      bit_nat(cc)
    case 1n+pp:
      match aa bb ff:
        case WCon{ab, at} WCon{bb2, bt} False{}:
          adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))
        case WCon{ab, at} WCon{bb2, bt} True{}:
          adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))

# a full add's sum and twice its carry are its three bits
law fa_nat:
  for xx: Bool
  for yy: Bool
  for cc: Bool
  {Nat.add(bit_nat(fa_s(Bool.full_add(xx, yy, cc))), Nat.double(bit_nat(fa_k(Bool.full_add(xx, yy, cc))))) ==
    Nat.add(bit_nat(xx), Nat.add(bit_nat(yy), bit_nat(cc))) : Nat}

def fa_nat(xx, yy, cc):
  match xx yy cc:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

# adc's cell, from a full add not yet known
law adc_eta:
  for pp: Nat
  for at: Word(pp)
  for bt: Word(pp)
  for ff: Bool
  for sk: Bool & Bool
  {Word.adc.con(pp, at, bt, ff, sk) == WCon{fa_s(sk), Word.adc(pp, at, bt, ff, fa_k(sk))} : Word(1n+pp)}

def adc_eta(_pp, _at, _bt, _ff, sk):
  (_ss, _kk) = sk
  {==}

# adc as Nats: the sum, and its carry out times 2^nn, is a, b (or its
# complement) and the carry in
law w_adc:
  for +nn: Nat
  for aa: Word(nn)
  for bb: Word(nn)
  for ff: Bool
  for +cc: Bool
  {Nat.add(Word.to_nat(nn, Word.adc(nn, aa, bb, ff, cc)), Nat.mul(adc_k(nn, aa, bb, ff, cc), M3.pow2(nn))) ==
    Nat.add(Word.to_nat(nn, aa), Nat.add(Word.to_nat(nn, adc_sel(nn, bb, ff)), bit_nat(cc))) : Nat}

def w_adc(nn, aa, bb, ff, cc):
  match nn:
    case 0n:
      match aa bb:
        case WNil{} WNil{}:
          nat_mul_one(bit_nat(cc))
    case 1n+(+pp):
      match aa bb ff:
        case WCon{+ab, +at} WCon{+bb2, +bt} False{}:
          Equal.trans(Nat, Nat.add(Word.to_nat(1n+pp, Word.adc.con(pp, at, bt, False{}, Bool.full_add(ab, bb2, cc))),
            Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), Nat.double(M3.pow2(pp)))),
            Nat.add(Word.to_nat(1n+pp, WCon{fa_s(Bool.full_add(ab, bb2, cc)), Word.adc(pp, at, bt, False{},
            fa_k(Bool.full_add(ab, bb2, cc)))}), Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))),
            Nat.double(M3.pow2(pp)))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2,
            bt}), bit_nat(cc))), Equal.cong(Word(1n+pp), Nat, z12 => Nat.add(Word.to_nat(1n+pp, z12), Nat.mul(adc_k(pp,
            at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), Nat.double(M3.pow2(pp)))), Word.adc.con(pp, at, bt,
            False{}, Bool.full_add(ab, bb2, cc)), WCon{fa_s(Bool.full_add(ab, bb2, cc)), Word.adc(pp, at, bt, False{},
            fa_k(Bool.full_add(ab, bb2, cc)))}, adc_eta(pp, at, bt, False{}, Bool.full_add(ab, bb2, cc))),
            Equal.trans(Nat, Nat.add(Word.to_nat(1n+pp, WCon{fa_s(Bool.full_add(ab, bb2, cc)), Word.adc(pp, at, bt,
            False{}, fa_k(Bool.full_add(ab, bb2, cc)))}), Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab,
            bb2, cc))), Nat.double(M3.pow2(pp)))), Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))))),
            Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), Nat.double(M3.pow2(pp)))),
            Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}), bit_nat(cc))),
            Equal.cong(Nat, Nat, z13 => Nat.add(z13, Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2,
            cc))), Nat.double(M3.pow2(pp)))), Word.to_nat(1n+pp, WCon{fa_s(Bool.full_add(ab, bb2, cc)), Word.adc(pp, at,
            bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))}), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))))),
            w_nat_con(pp, fa_s(Bool.full_add(ab, bb2, cc)), Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2,
            cc))))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))))),
            Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), Nat.double(M3.pow2(pp)))),
            Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt,
            False{}, fa_k(Bool.full_add(ab, bb2, cc)))))), Nat.double(Nat.mul(adc_k(pp, at, bt, False{},
            fa_k(Bool.full_add(ab, bb2, cc))), M3.pow2(pp)))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}),
            Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}), bit_nat(cc))), Equal.cong(Nat, Nat,
            z14 => Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Word.to_nat(pp, Word.adc(pp,
            at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))))), z14), Nat.mul(adc_k(pp, at, bt, False{},
            fa_k(Bool.full_add(ab, bb2, cc))), Nat.double(M3.pow2(pp))), Nat.double(Nat.mul(adc_k(pp, at, bt, False{},
            fa_k(Bool.full_add(ab, bb2, cc))), M3.pow2(pp))), nat_mul_double_r(adc_k(pp, at, bt, False{},
            fa_k(Bool.full_add(ab, bb2, cc))), M3.pow2(pp))), Equal.trans(Nat,
            Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt,
            False{}, fa_k(Bool.full_add(ab, bb2, cc)))))), Nat.double(Nat.mul(adc_k(pp, at, bt, False{},
            fa_k(Bool.full_add(ab, bb2, cc))), M3.pow2(pp)))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.add(Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))))),
            Nat.double(Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), M3.pow2(pp))))),
            Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}), bit_nat(cc))),
            M3.nat_add_assoc(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt,
            False{}, fa_k(Bool.full_add(ab, bb2, cc))))), Nat.double(Nat.mul(adc_k(pp, at, bt, False{},
            fa_k(Bool.full_add(ab, bb2, cc))), M3.pow2(pp)))), Equal.trans(Nat, Nat.add(bit_nat(fa_s(Bool.full_add(ab,
            bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2,
            cc))))), Nat.double(Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), M3.pow2(pp))))),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt,
            False{}, fa_k(Bool.full_add(ab, bb2, cc)))), Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2,
            cc))), M3.pow2(pp))))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}),
            bit_nat(cc))), Equal.cong(Nat, Nat, z15 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), z15),
            Nat.add(Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))))),
            Nat.double(Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), M3.pow2(pp)))),
            Nat.double(Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))),
            Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), M3.pow2(pp)))), Equal.sym(Nat,
            Nat.double(Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))),
            Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), M3.pow2(pp)))),
            Nat.add(Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))))),
            Nat.double(Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), M3.pow2(pp)))),
            M3.nat_double_add(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))),
            Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), M3.pow2(pp))))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt,
            False{}, fa_k(Bool.full_add(ab, bb2, cc)))), Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2,
            cc))), M3.pow2(pp))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
                Nat.double(Nat.add(Word.to_nat(pp,
            at), Nat.add(Word.to_nat(pp, adc_sel(pp, bt, False{})), bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))))),
            Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}), bit_nat(cc))),
            Equal.cong(Nat, Nat, z16 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(z16)),
            Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))), Nat.mul(adc_k(pp,
            at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), M3.pow2(pp))), Nat.add(Word.to_nat(pp, at),
            Nat.add(Word.to_nat(pp, adc_sel(pp, bt, False{})), bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), w_adc(pp,
            at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Nat.add(Word.to_nat(pp, at),
            Nat.add(Word.to_nat(pp, adc_sel(pp, bt, False{})), bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))))),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Nat.add(Word.to_nat(pp, adc_sel(pp, bt, False{})), bit_nat(fa_k(Bool.full_add(ab, bb2,
            cc))))))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}),
            bit_nat(cc))), Equal.cong(Nat, Nat, z17 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), z17),
            Nat.double(Nat.add(Word.to_nat(pp, at), Nat.add(Word.to_nat(pp, adc_sel(pp, bt, False{})),
            bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Nat.add(Word.to_nat(pp, adc_sel(pp, bt, False{})), bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))))),
            M3.nat_double_add(Word.to_nat(pp, at), Nat.add(Word.to_nat(pp, adc_sel(pp, bt, False{})),
            bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))))), Equal.trans(Nat, Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Nat.add(Word.to_nat(pp, adc_sel(pp, bt,
            False{})), bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))))), Nat.add(Word.to_nat(1n+pp, WCon{ab,
            at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}), bit_nat(cc))), Equal.cong(Nat, Nat,
            z18 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), z18)),
            Nat.double(Nat.add(Word.to_nat(pp, adc_sel(pp, bt, False{})), bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc))))), M3.nat_double_add(Word.to_nat(pp, adc_sel(pp, bt, False{})), bit_nat(fa_k(Bool.full_add(ab,
                bb2,
            cc))))), Equal.trans(Nat, Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))))), Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab,
            bb2, cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), Nat.add(Nat.double(Word.to_nat(pp,
            at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}),
            Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}), bit_nat(cc))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc))))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab,
            bb2, cc)))))), Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc))))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc))))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab,
            bb2, cc)))))), Equal.cong(Nat, Nat, z20 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), z20),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc)))))), Equal.cong(Nat, Nat, z19 => Nat.add(Nat.double(Word.to_nat(pp, at)), z19),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc))))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), {==})), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc))))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc))))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab,
            bb2, cc)))))), M3.nat_add_lcomm(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc)))))), Equal.cong(Nat, Nat, z22 => Nat.add(Nat.double(Word.to_nat(pp, at)), z22),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))))), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))),
            bit_nat(fa_s(Bool.full_add(ab, bb2, cc))))), Equal.trans(Nat, Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc)))))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2, cc))))),
            M3.nat_add_lcomm(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), Equal.cong(Nat, Nat,
            z21 => Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), z21),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2, cc)))),
            M3.nat_add_comm(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2,
            cc)))))))))), Equal.sym(Nat, Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))))), Equal.cong(Nat, Nat, z23 => Nat.add(z23, Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2, cc)))), M3.nat_add_comm(bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))))), Equal.trans(Nat,
            Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))))), Equal.cong(Nat, Nat, z24 => Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2,
            cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2, cc)))), z24), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), {==}), Equal.trans(Nat,
            Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))))), M3.nat_add_assoc(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))),
            bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Equal.trans(Nat,
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab,
            bb2, cc)))))), Equal.cong(Nat, Nat, z26 => Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))),
            z26), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(fa_s(Bool.full_add(ab, bb2, cc))))),
            Equal.trans(Nat, Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp,
            at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            bit_nat(fa_s(Bool.full_add(ab, bb2, cc))))), M3.nat_add_lcomm(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), Equal.cong(Nat,
            Nat, z25 => Nat.add(Nat.double(Word.to_nat(pp, at)), z25), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc))), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), bit_nat(fa_s(Bool.full_add(ab, bb2, cc)))),
            M3.nat_add_comm(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))))))), Equal.trans(Nat, Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            bit_nat(fa_s(Bool.full_add(ab, bb2, cc)))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), bit_nat(fa_s(Bool.full_add(ab, bb2, cc)))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))))), M3.nat_add_lcomm(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), Nat.double(Word.to_nat(pp,
            at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc))))), Equal.cong(Nat, Nat, z27 => Nat.add(Nat.double(Word.to_nat(pp, at)), z27),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), bit_nat(fa_s(Bool.full_add(ab, bb2, cc))))), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))),
            bit_nat(fa_s(Bool.full_add(ab, bb2, cc))))), M3.nat_add_lcomm(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2,
            cc)))), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))))))))))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}),
            bit_nat(cc))), Equal.cong(Nat, Nat, z28 => Nat.add(z28, Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))), fa_nat(ab, bb2, cc)), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))))), Nat.add(Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.add(bit_nat(bb2),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc))), Nat.add(Word.to_nat(1n+pp, WCon{ab,
            at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}), bit_nat(cc))), Equal.trans(Nat,
            Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))))), Nat.add(Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))),
            Nat.add(Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc))),
            Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))))), Equal.cong(Nat, Nat, z30 => Nat.add(z30, Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc))), Equal.cong(Nat, Nat,
            z29 => Nat.add(bit_nat(ab), z29), Nat.add(bit_nat(bb2), bit_nat(cc)), Nat.add(bit_nat(bb2), bit_nat(cc)),
            {==})), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))))), Equal.cong(Nat, Nat, z31 => Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))), z31), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{})))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{})))), {==}), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(bit_nat(ab), Nat.add(Nat.add(bit_nat(bb2), bit_nat(cc)), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))))), M3.nat_add_assoc(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc)),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Equal.trans(Nat, Nat.add(bit_nat(ab), Nat.add(Nat.add(bit_nat(bb2), bit_nat(cc)),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))))),
            Nat.add(bit_nat(ab), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))))), Equal.cong(Nat, Nat, z35 => Nat.add(bit_nat(ab), z35), Nat.add(Nat.add(bit_nat(bb2),
            bit_nat(cc)), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.add(bit_nat(bb2), bit_nat(cc)))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(bb2),
            bit_nat(cc)), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))))), Nat.add(bit_nat(bb2), Nat.add(bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc)))),
            M3.nat_add_assoc(bit_nat(bb2), bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Equal.trans(Nat, Nat.add(bit_nat(bb2),
            Nat.add(bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{})))))), Nat.add(bit_nat(bb2), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(cc)))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(bit_nat(bb2), bit_nat(cc)))), Equal.cong(Nat, Nat, z33 => Nat.add(bit_nat(bb2), z33),
            Nat.add(bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), bit_nat(cc))), Equal.trans(Nat, Nat.add(bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            bit_nat(cc))), M3.nat_add_lcomm(bit_nat(cc), Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{})))), Equal.cong(Nat, Nat, z32 => Nat.add(Nat.double(Word.to_nat(pp, at)), z32),
            Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(cc)), M3.nat_add_comm(bit_nat(cc),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))))), Equal.trans(Nat, Nat.add(bit_nat(bb2),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(bit_nat(bb2),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(cc)))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(bit_nat(bb2), bit_nat(cc)))), M3.nat_add_lcomm(bit_nat(bb2), Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(cc))), Equal.cong(Nat, Nat,
            z34 => Nat.add(Nat.double(Word.to_nat(pp, at)), z34), Nat.add(bit_nat(bb2),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc))),
            M3.nat_add_lcomm(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(cc))))))),
            Equal.trans(Nat, Nat.add(bit_nat(ab), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(bit_nat(ab), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))))), M3.nat_add_lcomm(bit_nat(ab), Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc)))),
            Equal.cong(Nat, Nat, z36 => Nat.add(Nat.double(Word.to_nat(pp, at)), z36), Nat.add(bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc)))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc)))), M3.nat_add_lcomm(bit_nat(ab), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(bit_nat(bb2), bit_nat(cc))))))))), Equal.sym(Nat, Nat.add(Nat.add(bit_nat(ab),
            Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{})))), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc))))), Equal.trans(Nat,
            Nat.add(Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.add(bit_nat(bb2),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc))),
            Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)), Nat.add(Nat.add(bit_nat(bb2),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp,
            at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab),
            Nat.add(bit_nat(bb2), bit_nat(cc))))), Equal.cong(Nat, Nat, z38 => Nat.add(z38,
            Nat.add(Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc))),
            Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            bit_nat(ab)), M3.nat_add_comm(bit_nat(ab), Nat.double(Word.to_nat(pp, at)))), Equal.trans(Nat,
            Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)), Nat.add(Nat.add(bit_nat(bb2),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc))),
            Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))))), Equal.cong(Nat, Nat, z39 => Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)),
            z39), Nat.add(Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc))),
            Equal.trans(Nat, Nat.add(Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))),
            bit_nat(cc)), Nat.add(Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(bb2)),
            bit_nat(cc)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2),
            bit_nat(cc))), Equal.cong(Nat, Nat, z37 => Nat.add(z37, bit_nat(cc)), Nat.add(bit_nat(bb2),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), bit_nat(bb2)), M3.nat_add_comm(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))))), M3.nat_add_assoc(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(bb2),
            bit_nat(cc)))), Equal.trans(Nat, Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc)))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(bit_nat(ab), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))))), M3.nat_add_assoc(Nat.double(Word.to_nat(pp, at)), bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc)))),
            Equal.cong(Nat, Nat, z40 => Nat.add(Nat.double(Word.to_nat(pp, at)), z40), Nat.add(bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc)))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc)))), M3.nat_add_lcomm(bit_nat(ab), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(bit_nat(bb2), bit_nat(cc))))))))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab),
            Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{})))), bit_nat(cc))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Nat.add(bit_nat(bb2),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc))), Nat.add(Word.to_nat(1n+pp, WCon{ab,
            at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}), bit_nat(cc))), Equal.cong(Nat, Nat, z41 => Nat.add(z41,
            Nat.add(Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc))),
            Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))), Word.to_nat(1n+pp, WCon{ab, at}), Equal.sym(Nat,
            Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))), w_nat_con(pp, ab,
            at))), Equal.cong(Nat, Nat, z42 => Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(z42, bit_nat(cc))),
            Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), Word.to_nat(1n+pp, WCon{bb2,
            bt}), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{bb2, bt}), Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{})))), w_nat_con(pp, bb2, bt)))))))))))))))
        case WCon{+ab, +at} WCon{+bb2, +bt} True{}:
          Equal.trans(Nat, Nat.add(Word.to_nat(1n+pp, Word.adc.con(pp, at, bt, True{}, Bool.full_add(ab, Bool.not(bb2),
            cc))), Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(M3.pow2(pp)))), Nat.add(Word.to_nat(1n+pp, WCon{fa_s(Bool.full_add(ab, Bool.not(bb2), cc)),
            Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))}), Nat.mul(adc_k(pp, at, bt,
            True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(M3.pow2(pp)))), Nat.add(Word.to_nat(1n+pp,
            WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))),
            Equal.cong(Word(1n+pp), Nat, z43 => Nat.add(Word.to_nat(1n+pp, z43), Nat.mul(adc_k(pp, at, bt, True{},
            fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(M3.pow2(pp)))), Word.adc.con(pp, at, bt, True{},
            Bool.full_add(ab, Bool.not(bb2), cc)), WCon{fa_s(Bool.full_add(ab, Bool.not(bb2), cc)), Word.adc(pp, at,
            bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))}, adc_eta(pp, at, bt, True{}, Bool.full_add(ab,
            Bool.not(bb2), cc))), Equal.trans(Nat, Nat.add(Word.to_nat(1n+pp, WCon{fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)), Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))}),
            Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(M3.pow2(pp)))),
            Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Word.to_nat(pp,
            Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), Nat.mul(adc_k(pp, at, bt,
            True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(M3.pow2(pp)))), Nat.add(Word.to_nat(1n+pp,
            WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))),
            Equal.cong(Nat, Nat, z44 => Nat.add(z44, Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc))), Nat.double(M3.pow2(pp)))), Word.to_nat(1n+pp, WCon{fa_s(Bool.full_add(ab,
                Bool.not(bb2),
            cc)), Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))}),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Word.to_nat(pp, Word.adc(pp, at,
            bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), w_nat_con(pp, fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)), Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))),
            Equal.trans(Nat, Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))),
            Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(M3.pow2(pp)))),
            Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Word.to_nat(pp,
            Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), Nat.double(Nat.mul(adc_k(pp,
            at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), M3.pow2(pp)))), Nat.add(Word.to_nat(1n+pp,
            WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))),
            Equal.cong(Nat, Nat, z45 => Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))),
            z45), Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))),
                Nat.double(M3.pow2(pp))),
            Nat.double(Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), M3.pow2(pp))),
            nat_mul_double_r(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), M3.pow2(pp))),
            Equal.trans(Nat, Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))),
            Nat.double(Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), M3.pow2(pp)))),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp,
            Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.double(Nat.mul(adc_k(pp,
            at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), M3.pow2(pp))))), Nat.add(Word.to_nat(1n+pp,
            WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))),
            M3.nat_add_assoc(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Word.to_nat(pp,
                Word.adc(pp,
            at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.double(Nat.mul(adc_k(pp, at, bt, True{},
            fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), M3.pow2(pp)))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp,
            Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.double(Nat.mul(adc_k(pp,
            at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), M3.pow2(pp))))),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Nat.add(Word.to_nat(pp,
            Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.mul(adc_k(pp, at, bt,
            True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), M3.pow2(pp))))), Nat.add(Word.to_nat(1n+pp, WCon{ab,
            at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))), Equal.cong(Nat,
            Nat, z46 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), z46),
            Nat.add(Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2),
            cc))))), Nat.double(Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))),
            M3.pow2(pp)))), Nat.double(Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc)))), Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))),
            M3.pow2(pp)))), Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt, True{},
            fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc))), M3.pow2(pp)))), Nat.add(Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, True{},
            fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.double(Nat.mul(adc_k(pp, at, bt, True{},
            fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), M3.pow2(pp)))), M3.nat_double_add(Word.to_nat(pp, Word.adc(pp,
                at,
            bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.mul(adc_k(pp, at, bt, True{},
            fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), M3.pow2(pp))))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Nat.add(Word.to_nat(pp,
            Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.mul(adc_k(pp, at, bt,
            True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), M3.pow2(pp))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc))), Nat.double(Nat.add(Word.to_nat(pp, at), Nat.add(Word.to_nat(pp, adc_sel(pp, bt,
            True{})), bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))))), Nat.add(Word.to_nat(1n+pp, WCon{ab,
            at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))), Equal.cong(Nat,
            Nat, z47 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(z47)),
            Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), M3.pow2(pp))),
            Nat.add(Word.to_nat(pp, at), Nat.add(Word.to_nat(pp, adc_sel(pp, bt, True{})),
            bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), w_adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc)))), Equal.trans(Nat, Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(Nat.add(Word.to_nat(pp, at), Nat.add(Word.to_nat(pp, adc_sel(pp, bt, True{})),
            bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Nat.add(Word.to_nat(pp,
            adc_sel(pp, bt, True{})), bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))))),
            Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp,
            bt)}), bit_nat(cc))), Equal.cong(Nat, Nat, z48 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2),
            cc))), z48), Nat.double(Nat.add(Word.to_nat(pp, at), Nat.add(Word.to_nat(pp, adc_sel(pp, bt, True{})),
            bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Nat.add(Word.to_nat(pp, adc_sel(pp, bt, True{})), bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2),
            cc)))))), M3.nat_double_add(Word.to_nat(pp, at), Nat.add(Word.to_nat(pp, adc_sel(pp, bt, True{})),
            bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Nat.add(Word.to_nat(pp, adc_sel(pp, bt, True{})), bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2),
            cc))))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp,
            at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))))), Nat.add(Word.to_nat(1n+pp, WCon{ab,
            at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))), Equal.cong(Nat,
            Nat, z49 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp,
            at)), z49)), Nat.double(Nat.add(Word.to_nat(pp, adc_sel(pp, bt, True{})), bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc))))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), M3.nat_double_add(Word.to_nat(pp,
            adc_sel(pp, bt, True{})), bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc))))))), Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}),
            Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc))))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))))), Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Equal.trans(Nat, Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))))), Equal.cong(Nat, Nat, z51 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2),
            cc))), z51), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), Equal.cong(Nat, Nat,
            z50 => Nat.add(Nat.double(Word.to_nat(pp, at)), z50), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc))))), {==})), Equal.trans(Nat, Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2),
            cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc))))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))))), M3.nat_add_lcomm(bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc))), Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), Equal.cong(Nat, Nat,
            z53 => Nat.add(Nat.double(Word.to_nat(pp, at)), z53), Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2),
            cc))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp,
            bt, True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc))))), M3.nat_add_lcomm(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc))))), Equal.cong(Nat, Nat, z52 => Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), z52), Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))), M3.nat_add_comm(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))))))), Equal.sym(Nat,
            Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2),
            cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.add(Nat.double(Word.to_nat(pp,
            at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))))), Equal.cong(Nat, Nat, z54 => Nat.add(z54, Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))), M3.nat_add_comm(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), Equal.trans(Nat,
            Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))))), Equal.cong(Nat, Nat,
            z55 => Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))), z55), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), {==}), Equal.trans(Nat,
            Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc)))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))))), M3.nat_add_assoc(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Equal.trans(Nat,
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))))), Equal.cong(Nat, Nat, z57 => Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc)))), z57), Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))))),
            M3.nat_add_lcomm(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), Equal.cong(Nat, Nat,
            z56 => Nat.add(Nat.double(Word.to_nat(pp, at)), z56), Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2),
            cc))), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))),
            M3.nat_add_comm(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Word.to_nat(pp, adc_sel(pp,
            bt, True{}))))))), Equal.trans(Nat, Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2),
            cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))))), M3.nat_add_lcomm(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))))), Equal.cong(Nat, Nat,
            z58 => Nat.add(Nat.double(Word.to_nat(pp, at)), z58), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc)))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))))),
            M3.nat_add_lcomm(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))))))))))), Equal.trans(Nat,
            Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Nat.add(bit_nat(ab),
            Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}),
            Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))), Equal.cong(Nat, Nat,
            z59 => Nat.add(z59, Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.add(bit_nat(ab),
            Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))), fa_nat(ab, Bool.not(bb2), cc)), Equal.trans(Nat,
            Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.add(bit_nat(Bool.not(bb2)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), bit_nat(cc))), Nat.add(Word.to_nat(1n+pp, WCon{ab,
            at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))), Equal.trans(Nat,
            Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))))), Nat.add(Nat.add(bit_nat(ab),
            Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{})))), bit_nat(cc))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab),
            Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Nat.add(bit_nat(Bool.not(bb2)),
            Nat.add(bit_nat(ab), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))))),
            Equal.cong(Nat, Nat, z61 => Nat.add(z61, Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(bit_nat(ab),
            Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))), Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab),
            bit_nat(cc))), Equal.trans(Nat, Nat.add(bit_nat(ab), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))),
            Nat.add(bit_nat(ab), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))), Nat.add(bit_nat(Bool.not(bb2)),
            Nat.add(bit_nat(ab), bit_nat(cc))), Equal.cong(Nat, Nat, z60 => Nat.add(bit_nat(ab), z60),
            Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc)), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc)), {==}),
            M3.nat_add_lcomm(bit_nat(ab), bit_nat(Bool.not(bb2)), bit_nat(cc)))), Equal.trans(Nat,
            Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))))), Equal.cong(Nat, Nat,
            z62 => Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))), z62),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), {==}),
            Equal.trans(Nat, Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(bit_nat(Bool.not(bb2)), Nat.add(Nat.add(bit_nat(ab), bit_nat(cc)),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))))),
                M3.nat_add_assoc(bit_nat(Bool.not(bb2)),
            Nat.add(bit_nat(ab), bit_nat(cc)), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))))), Equal.trans(Nat, Nat.add(bit_nat(Bool.not(bb2)), Nat.add(Nat.add(bit_nat(ab),
            bit_nat(cc)), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{})))))), Nat.add(bit_nat(Bool.not(bb2)), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))))), Equal.cong(Nat, Nat,
            z66 => Nat.add(bit_nat(Bool.not(bb2)), z66), Nat.add(Nat.add(bit_nat(ab), bit_nat(cc)),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(bit_nat(ab), bit_nat(cc)))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab), bit_nat(cc)),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(bit_nat(ab), Nat.add(bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc)))),
            M3.nat_add_assoc(bit_nat(ab), bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, at)),
                Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))))), Equal.trans(Nat, Nat.add(bit_nat(ab), Nat.add(bit_nat(cc),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))))),
            Nat.add(bit_nat(ab), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc)))),
            Equal.cong(Nat, Nat, z64 => Nat.add(bit_nat(ab), z64), Nat.add(bit_nat(cc),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            bit_nat(cc))), Equal.trans(Nat, Nat.add(bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            bit_nat(cc))), M3.nat_add_lcomm(bit_nat(cc), Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{})))), Equal.cong(Nat, Nat, z63 => Nat.add(Nat.double(Word.to_nat(pp, at)), z63),
            Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), bit_nat(cc)), M3.nat_add_comm(bit_nat(cc),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))))), Equal.trans(Nat, Nat.add(bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), bit_nat(cc)))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(bit_nat(ab), bit_nat(cc)))), M3.nat_add_lcomm(bit_nat(ab), Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), bit_nat(cc))), Equal.cong(Nat, Nat,
            z65 => Nat.add(Nat.double(Word.to_nat(pp, at)), z65), Nat.add(bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc))),
            M3.nat_add_lcomm(bit_nat(ab), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), bit_nat(cc))))))),
            Equal.trans(Nat, Nat.add(bit_nat(Bool.not(bb2)), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(bit_nat(Bool.not(bb2)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            Nat.add(bit_nat(ab), bit_nat(cc))))), M3.nat_add_lcomm(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp,
            at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc)))),
            Equal.cong(Nat, Nat, z67 => Nat.add(Nat.double(Word.to_nat(pp, at)), z67), Nat.add(bit_nat(Bool.not(bb2)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc)))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            Nat.add(bit_nat(ab), bit_nat(cc)))), M3.nat_add_lcomm(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc))))))))), Equal.sym(Nat,
            Nat.add(Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.add(bit_nat(Bool.not(bb2)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp,
            at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            Nat.add(bit_nat(ab), bit_nat(cc))))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab),
            Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{})))), bit_nat(cc))), Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)),
            Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))),
            bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))))), Equal.cong(Nat, Nat,
            z69 => Nat.add(z69, Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{})))), bit_nat(cc))), Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)), M3.nat_add_comm(bit_nat(ab),
                Nat.double(Word.to_nat(pp,
            at)))), Equal.trans(Nat, Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)),
            Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))),
            bit_nat(cc))), Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))))), Equal.cong(Nat, Nat,
            z70 => Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)), z70),
            Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))),
            bit_nat(cc)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            bit_nat(cc))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{})))), bit_nat(cc)), Nat.add(Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), bit_nat(Bool.not(bb2))), bit_nat(cc)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))), Equal.cong(Nat, Nat, z68 => Nat.add(z68,
            bit_nat(cc)), Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), bit_nat(Bool.not(bb2))),
            M3.nat_add_comm(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            M3.nat_add_assoc(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), bit_nat(Bool.not(bb2)),
                bit_nat(cc)))),
            Equal.trans(Nat, Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            bit_nat(cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp,
            bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))))),
            M3.nat_add_assoc(Nat.double(Word.to_nat(pp, at)), bit_nat(ab), Nat.add(Nat.double(Word.to_nat(pp,
                adc_sel(pp,
            bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc)))), Equal.cong(Nat, Nat,
            z72 => Nat.add(Nat.double(Word.to_nat(pp, at)), z72), Nat.add(bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc)))), Equal.trans(Nat, Nat.add(bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab),
            Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc)))),
                M3.nat_add_lcomm(bit_nat(ab),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))),
            Equal.cong(Nat, Nat, z71 => Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), z71),
            Nat.add(bit_nat(ab), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))), Nat.add(bit_nat(Bool.not(bb2)),
            Nat.add(bit_nat(ab), bit_nat(cc))), M3.nat_add_lcomm(bit_nat(ab), bit_nat(Bool.not(bb2)),
            bit_nat(cc)))))))))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))),
            Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))),
            bit_nat(cc))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Nat.add(bit_nat(Bool.not(bb2)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), bit_nat(cc))), Nat.add(Word.to_nat(1n+pp, WCon{ab,
            at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))), Equal.cong(Nat,
            Nat, z73 => Nat.add(z73, Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{})))), bit_nat(cc))), Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))), Word.to_nat(1n+pp,
            WCon{ab, at}), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(bit_nat(ab),
            Nat.double(Word.to_nat(pp, at))), w_nat_con(pp, ab, at))), Equal.cong(Nat, Nat,
            z74 => Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(z74, bit_nat(cc))),
            Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), Word.to_nat(1n+pp,
            WCon{Bool.not(bb2), Word.not(pp, bt)}), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp,
            bt)}), Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), w_nat_con(pp,
            Bool.not(bb2), Word.not(pp, bt))))))))))))))))

# w_adc, with 2^nn named through uu
law w_adc_u:
  for +nn: Nat
  for uu: Unit
  for aa: Word(nn)
  for bb: Word(nn)
  for ff: Bool
  for cc: Bool
  {Nat.add(Word.to_nat(nn, Word.adc(nn, aa, bb, ff, cc)), Nat.mul(adc_k(nn, aa, bb, ff, cc), M3.pow2u(nn, uu))) ==
    Nat.add(Word.to_nat(nn, aa), Nat.add(Word.to_nat(nn, adc_sel(nn, bb, ff)), bit_nat(cc))) : Nat}

def w_adc_u(nn, uu, aa, bb, ff, cc):
  match uu:
    case Unit{}:
      w_adc(nn, aa, bb, ff, cc)

# the carry out of a U32 sum
def uadd_k(aa: U32, bb: U32) -> Nat:
  match aa bb:
    case U32{xw} U32{yw}:
      adc_k(32n, xw, yw, False{}, False{})

# a U32 sum, and its carry times 2^32, is the Nat sum
law u_add:
  for +uu: Unit
  for aa: U32
  for bb: U32
  {Nat.add(U32.to_nat(U32.add(aa, bb)), Nat.mul(uadd_k(aa, bb), M3.pow2u(32n, uu))) ==
    Nat.add(U32.to_nat(aa), U32.to_nat(bb)) : Nat}

def u_add(uu, aa, bb):
  match aa bb:
    case U32{+xw} U32{+yw}:
      Equal.trans(Nat, Nat.add(Word.to_nat(32n, Word.adc(32n, xw, yw, False{}, False{})),
        Nat.mul(adc_k(32n, xw, yw, False{}, False{}), M3.pow2u(32n, uu))),
        Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, yw), 0n)),
        Nat.add(Word.to_nat(32n, xw), Word.to_nat(32n, yw)),
        w_adc_u(32n, uu, xw, yw, False{}, False{}),
        Equal.cong(Nat, Nat, zz => Nat.add(Word.to_nat(32n, xw), zz), Nat.add(Word.to_nat(32n, yw), 0n),
          Word.to_nat(32n, yw), M3.nat_add_zero(Word.to_nat(32n, yw))))

# the borrow count of a U32 difference
def usub_k(aa: U32, bb: U32) -> Nat:
  match aa bb:
    case U32{xw} U32{yw}:
      adc_k(32n, xw, yw, True{}, True{})

# a U32 difference, its borrow count times 2^32 and what it takes away make
# the first U32 and 2^32
law u_sub:
  for +uu: Unit
  for aa: U32
  for bb: U32
  {Nat.add(U32.to_nat(U32.sub(aa, bb)), Nat.add(Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)), U32.to_nat(bb))) ==
    Nat.add(U32.to_nat(aa), M3.pow2u(32n, uu)) : Nat}

def u_sub(uu, aa, bb):
  match aa bb:
    case U32{+xw} U32{+yw}:
      Equal.trans(Nat, Nat.add(Word.to_nat(32n, Word.adc(32n, xw, yw, True{}, True{})), Nat.add(Nat.mul(adc_k(32n, xw,
        yw, True{}, True{}), M3.pow2u(32n, uu)), Word.to_nat(32n, yw))), Nat.add(Nat.add(Word.to_nat(32n, Word.adc(32n,
        xw, yw, True{}, True{})), Nat.mul(adc_k(32n, xw, yw, True{}, True{}), M3.pow2u(32n, uu))), Word.to_nat(32n,
            yw)),
        Nat.add(Word.to_nat(32n, xw), M3.pow2u(32n, uu)), Equal.sym(Nat, Nat.add(Nat.add(Word.to_nat(32n, Word.adc(32n,
        xw, yw, True{}, True{})), Nat.mul(adc_k(32n, xw, yw, True{}, True{}), M3.pow2u(32n, uu))), Word.to_nat(32n,
            yw)),
        Nat.add(Word.to_nat(32n, Word.adc(32n, xw, yw, True{}, True{})), Nat.add(Nat.mul(adc_k(32n, xw, yw, True{},
        True{}), M3.pow2u(32n, uu)), Word.to_nat(32n, yw))), M3.nat_add_assoc(Word.to_nat(32n, Word.adc(32n, xw, yw,
            True{},
        True{})), Nat.mul(adc_k(32n, xw, yw, True{}, True{}), M3.pow2u(32n, uu)), Word.to_nat(32n, yw))),
            Equal.trans(Nat,
        Nat.add(Nat.add(Word.to_nat(32n, Word.adc(32n, xw, yw, True{}, True{})), Nat.mul(adc_k(32n, xw, yw, True{},
        True{}), M3.pow2u(32n, uu))), Word.to_nat(32n, yw)), Nat.add(Nat.add(Word.to_nat(32n, xw),
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), 1n)), Word.to_nat(32n, yw)), Nat.add(Word.to_nat(32n, xw),
        M3.pow2u(32n, uu)), Equal.cong(Nat, Nat, z75 => Nat.add(z75, Word.to_nat(32n, yw)), Nat.add(Word.to_nat(32n,
        Word.adc(32n, xw, yw, True{}, True{})), Nat.mul(adc_k(32n, xw, yw, True{}, True{}), M3.pow2u(32n, uu))),
        Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n, yw)), 1n)), w_adc_u(32n, uu, xw, yw,
        True{}, True{})), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n,
        yw)), 1n)), Word.to_nat(32n, yw)), Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n, yw)),
        Nat.add(Word.to_nat(32n, yw), 1n))), Nat.add(Word.to_nat(32n, xw), M3.pow2u(32n, uu)), Equal.trans(Nat,
        Nat.add(Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n, yw)), 1n)), Word.to_nat(32n, yw)),
        Nat.add(1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, xw), Word.to_nat(32n, yw)))),
        Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, yw), 1n))),
        Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n, yw)), 1n)),
        Word.to_nat(32n, yw)), Nat.add(Nat.add(1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, xw))),
        Word.to_nat(32n, yw)), Nat.add(1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, xw),
        Word.to_nat(32n, yw)))), Equal.cong(Nat, Nat, z78 => Nat.add(z78, Word.to_nat(32n, yw)),
        Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n, yw)), 1n)), Nat.add(1n,
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, xw))), Equal.trans(Nat, Nat.add(Word.to_nat(32n,
        xw), Nat.add(Word.to_nat(32n, Word.not(32n, yw)), 1n)), Nat.add(Word.to_nat(32n, xw), Nat.add(1n,
        Word.to_nat(32n, Word.not(32n, yw)))), Nat.add(1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)),
        Word.to_nat(32n, xw))), Equal.cong(Nat, Nat, z76 => Nat.add(Word.to_nat(32n, xw), z76),
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), 1n), Nat.add(1n, Word.to_nat(32n, Word.not(32n, yw))),
        M3.nat_add_comm(Word.to_nat(32n, Word.not(32n, yw)), 1n)), Equal.trans(Nat, Nat.add(Word.to_nat(32n, xw),
        Nat.add(1n, Word.to_nat(32n, Word.not(32n, yw)))), Nat.add(1n, Nat.add(Word.to_nat(32n, xw), Word.to_nat(32n,
        Word.not(32n, yw)))), Nat.add(1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, xw))),
        M3.nat_add_lcomm(Word.to_nat(32n, xw), 1n, Word.to_nat(32n, Word.not(32n, yw))), Equal.cong(Nat, Nat,
        z77 => Nat.add(1n, z77), Nat.add(Word.to_nat(32n, xw), Word.to_nat(32n, Word.not(32n, yw))),
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, xw)), M3.nat_add_comm(Word.to_nat(32n, xw),
        Word.to_nat(32n, Word.not(32n, yw))))))), Equal.trans(Nat, Nat.add(Nat.add(1n, Nat.add(Word.to_nat(32n,
        Word.not(32n, yw)), Word.to_nat(32n, xw))), Word.to_nat(32n, yw)), Nat.add(1n, Nat.add(Nat.add(Word.to_nat(32n,
        Word.not(32n, yw)), Word.to_nat(32n, xw)), Word.to_nat(32n, yw))), Nat.add(1n, Nat.add(Word.to_nat(32n,
        Word.not(32n, yw)), Nat.add(Word.to_nat(32n, xw), Word.to_nat(32n, yw)))), M3.nat_add_assoc(1n,
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, xw)), Word.to_nat(32n, yw)), Equal.cong(Nat, Nat,
        z79 => Nat.add(1n, z79), Nat.add(Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, xw)),
        Word.to_nat(32n, yw)), Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, xw),
        Word.to_nat(32n, yw))), M3.nat_add_assoc(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, xw),
        Word.to_nat(32n, yw))))), Equal.sym(Nat, Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n,
        yw)), Nat.add(Word.to_nat(32n, yw), 1n))), Nat.add(1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)),
        Nat.add(Word.to_nat(32n, xw), Word.to_nat(32n, yw)))), Equal.trans(Nat, Nat.add(Word.to_nat(32n, xw),
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, yw), 1n))), Nat.add(Word.to_nat(32n, xw),
        Nat.add(1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, yw)))), Nat.add(1n,
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, xw), Word.to_nat(32n, yw)))),
        Equal.cong(Nat, Nat, z81 => Nat.add(Word.to_nat(32n, xw), z81), Nat.add(Word.to_nat(32n, Word.not(32n, yw)),
        Nat.add(Word.to_nat(32n, yw), 1n)), Nat.add(1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n,
        yw))), Equal.trans(Nat, Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, yw), 1n)),
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(1n, Word.to_nat(32n, yw))), Nat.add(1n,
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, yw))), Equal.cong(Nat, Nat,
        z80 => Nat.add(Word.to_nat(32n, Word.not(32n, yw)), z80), Nat.add(Word.to_nat(32n, yw), 1n), Nat.add(1n,
        Word.to_nat(32n, yw)), M3.nat_add_comm(Word.to_nat(32n, yw), 1n)), M3.nat_add_lcomm(Word.to_nat(32n,
            Word.not(32n,
        yw)), 1n, Word.to_nat(32n, yw)))), Equal.trans(Nat, Nat.add(Word.to_nat(32n, xw), Nat.add(1n,
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, yw)))), Nat.add(1n, Nat.add(Word.to_nat(32n, xw),
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, yw)))), Nat.add(1n, Nat.add(Word.to_nat(32n,
        Word.not(32n, yw)), Nat.add(Word.to_nat(32n, xw), Word.to_nat(32n, yw)))), M3.nat_add_lcomm(Word.to_nat(32n,
            xw),
        1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, yw))), Equal.cong(Nat, Nat,
        z82 => Nat.add(1n, z82), Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n, yw)),
        Word.to_nat(32n, yw))), Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, xw),
        Word.to_nat(32n, yw))), M3.nat_add_lcomm(Word.to_nat(32n, xw), Word.to_nat(32n, Word.not(32n, yw)),
        Word.to_nat(32n, yw))))))), Equal.cong(Nat, Nat, z83 => Nat.add(Word.to_nat(32n, xw), z83),
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, yw), 1n)), M3.pow2u(32n, uu), w_not_u(32n,
        uu, yw)))))

# laws/AsU32ReadsPlainDigits.bend: word multiplication as Nat multiplication

# the bit shl.put shifts out, as a Nat
def put_top(nn: Nat, ww: Word(nn), cc: Bool) -> Nat:
  match nn:
    case 0n:
      bit_nat(cc)
    case 1n+pp:
      match ww:
        case WCon{bb, tt}:
          put_top(pp, tt, bb)

# shl.put as Nats: c and twice w, less the bit shifted out
law w_put:
  for +nn: Nat
  for ww: Word(nn)
  for +cc: Bool
  {Nat.add(Word.to_nat(nn, Word.shl.put(nn, cc, ww)), Nat.mul(put_top(nn, ww, cc), M3.pow2(nn))) ==
    Nat.add(bit_nat(cc), Nat.double(Word.to_nat(nn, ww))) : Nat}

def w_put(nn, ww, cc):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          Equal.trans(Nat, Nat.mul(bit_nat(cc), 1n), bit_nat(cc), Nat.add(bit_nat(cc), 0n), nat_mul_one(bit_nat(cc)),
            Equal.sym(Nat, Nat.add(bit_nat(cc), 0n), bit_nat(cc), M3.nat_add_zero(bit_nat(cc))))
    case 1n+(+pp):
      match ww:
        case WCon{+bb, +tt}:
          Equal.trans(Nat, Nat.add(Word.to_nat(1n+pp, WCon{cc, Word.shl.put(pp, bb, tt)}), Nat.mul(put_top(pp, tt, bb),
            Nat.double(M3.pow2(pp)))), Nat.add(Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb,
            tt)))), Nat.mul(put_top(pp, tt, bb), Nat.double(M3.pow2(pp)))), Nat.add(bit_nat(cc),
            Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))), Equal.cong(Nat, Nat, z84 => Nat.add(z84, Nat.mul(put_top(pp,
            tt, bb), Nat.double(M3.pow2(pp)))), Word.to_nat(1n+pp, WCon{cc, Word.shl.put(pp, bb, tt)}),
            Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt)))), w_nat_con(pp, cc,
            Word.shl.put(pp, bb, tt))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp,
            Word.shl.put(pp, bb, tt)))), Nat.mul(put_top(pp, tt, bb), Nat.double(M3.pow2(pp)))),
            Nat.add(Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt)))),
            Nat.double(Nat.mul(put_top(pp, tt, bb), M3.pow2(pp)))), Nat.add(bit_nat(cc), Nat.double(Word.to_nat(1n+pp,
            WCon{bb, tt}))), Equal.cong(Nat, Nat, z85 => Nat.add(Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp,
            Word.shl.put(pp, bb, tt)))), z85), Nat.mul(put_top(pp, tt, bb), Nat.double(M3.pow2(pp))),
            Nat.double(Nat.mul(put_top(pp, tt, bb), M3.pow2(pp))), nat_mul_double_r(put_top(pp, tt, bb), M3.pow2(pp))),
            Equal.trans(Nat, Nat.add(Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt)))),
            Nat.double(Nat.mul(put_top(pp, tt, bb), M3.pow2(pp)))), Nat.add(bit_nat(cc),
            Nat.add(Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt))), Nat.double(Nat.mul(put_top(pp, tt, bb),
            M3.pow2(pp))))), Nat.add(bit_nat(cc), Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))),
            M3.nat_add_assoc(bit_nat(cc), Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt))),
            Nat.double(Nat.mul(put_top(pp, tt, bb), M3.pow2(pp)))), Equal.trans(Nat, Nat.add(bit_nat(cc),
            Nat.add(Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt))), Nat.double(Nat.mul(put_top(pp, tt, bb),
            M3.pow2(pp))))), Nat.add(bit_nat(cc), Nat.double(Nat.add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)),
            Nat.mul(put_top(pp, tt, bb), M3.pow2(pp))))), Nat.add(bit_nat(cc), Nat.double(Word.to_nat(1n+pp, WCon{bb,
            tt}))), Equal.cong(Nat, Nat, z86 => Nat.add(bit_nat(cc), z86), Nat.add(Nat.double(Word.to_nat(pp,
            Word.shl.put(pp, bb, tt))), Nat.double(Nat.mul(put_top(pp, tt, bb), M3.pow2(pp)))),
            Nat.double(Nat.add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb), M3.pow2(pp)))),
            Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb),
            M3.pow2(pp)))), Nat.add(Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt))),
                Nat.double(Nat.mul(put_top(pp,
            tt, bb), M3.pow2(pp)))), M3.nat_double_add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp,
                tt,
            bb), M3.pow2(pp))))), Equal.trans(Nat, Nat.add(bit_nat(cc), Nat.double(Nat.add(Word.to_nat(pp,
            Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb), M3.pow2(pp))))), Nat.add(bit_nat(cc),
            Nat.double(Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, tt))))), Nat.add(bit_nat(cc),
            Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))), Equal.cong(Nat, Nat, z87 => Nat.add(bit_nat(cc),
            Nat.double(z87)), Nat.add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb),
            M3.pow2(pp))), Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, tt))), w_put(pp, tt, bb)), Equal.cong(Nat,
                Nat,
            z88 => Nat.add(bit_nat(cc), Nat.double(z88)), Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, tt))),
            Word.to_nat(1n+pp, WCon{bb, tt}), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{bb, tt}), Nat.add(bit_nat(bb),
            Nat.double(Word.to_nat(pp, tt))), w_nat_con(pp, bb, tt))))))))

# the bit shl shifts out, as a Nat
def shl_top(nn: Nat, ww: Word(nn)) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+pp:
      match ww:
        case WCon{bb, tt}:
          put_top(pp, tt, bb)

# shl as Nats: twice w, less the bit shifted out
law w_shl:
  for +nn: Nat
  for ww: Word(nn)
  {Nat.add(Word.to_nat(nn, Word.shl(nn, ww)), Nat.mul(shl_top(nn, ww), M3.pow2(nn))) ==
    Nat.double(Word.to_nat(nn, ww)) : Nat}

def w_shl(nn, ww):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match ww:
        case WCon{+bb, +tt}:
          Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt))), Nat.mul(put_top(pp, tt, bb),
            Nat.double(M3.pow2(pp)))), Nat.add(Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt))),
            Nat.double(Nat.mul(put_top(pp, tt, bb), M3.pow2(pp)))), Nat.double(Word.to_nat(1n+pp, WCon{bb, tt})),
            Equal.cong(Nat, Nat, z89 => Nat.add(Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt))), z89),
            Nat.mul(put_top(pp, tt, bb), Nat.double(M3.pow2(pp))), Nat.double(Nat.mul(put_top(pp, tt, bb),
                M3.pow2(pp))),
            nat_mul_double_r(put_top(pp, tt, bb), M3.pow2(pp))), Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(pp,
            Word.shl.put(pp, bb, tt))), Nat.double(Nat.mul(put_top(pp, tt, bb), M3.pow2(pp)))),
            Nat.double(Nat.add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb), M3.pow2(pp)))),
            Nat.double(Word.to_nat(1n+pp, WCon{bb, tt})), Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(pp,
            Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb), M3.pow2(pp)))), Nat.add(Nat.double(Word.to_nat(pp,
            Word.shl.put(pp, bb, tt))), Nat.double(Nat.mul(put_top(pp, tt, bb), M3.pow2(pp)))),
            M3.nat_double_add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb), M3.pow2(pp)))),
            Equal.trans(Nat, Nat.double(Nat.add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb),
            M3.pow2(pp)))), Nat.double(Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, tt)))),
            Nat.double(Word.to_nat(1n+pp, WCon{bb, tt})), Equal.cong(Nat, Nat, z90 => Nat.double(z90),
            Nat.add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb), M3.pow2(pp))),
            Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, tt))), w_put(pp, tt, bb)), Equal.cong(Nat, Nat,
            z91 => Nat.double(z91), Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, tt))), Word.to_nat(1n+pp, WCon{bb,
            tt}), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{bb, tt}), Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp,
            tt))), w_nat_con(pp, bb, tt))))))

# how many times 2^nn mul.go's product passes
def mul_k(+nn: Nat, mm: Nat, aa: Word(mm), +bb: Word(nn), +acc: Word(nn)) -> Nat:
  match mm:
    case 0n:
      0n
    case 1n+(+mp):
      match aa:
        case WCon{False{}, +at}:
          Nat.add(mul_k(nn, mp, at, Word.shl(nn, bb), acc), Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)))
        case WCon{True{}, +at}:
          Nat.add(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), adc_k(nn, acc, bb, False{}, False{})))

# mul.go as Nats: the product, and how many times it passes 2^nn, is acc and
# a times b
law w_mulgo:
  for +nn: Nat
  for mm: Nat
  for aa: Word(mm)
  for +bb: Word(nn)
  for +acc: Word(nn)
  {Nat.add(Word.to_nat(nn, Word.mul.go(nn, mm, aa, bb, acc)), Nat.mul(mul_k(nn, mm, aa, bb, acc), M3.pow2(nn))) ==
    Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mm, aa), Word.to_nat(nn, bb))) : Nat}

def w_mulgo(nn, mm, aa, bb, acc):
  match mm:
    case 0n:
      match aa:
        case WNil{}:
          {==}
    case 1n+(+mp):
      match aa:
        case WCon{False{}, +at}:
          Equal.trans(Nat, Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), acc)),
            Nat.mul(Nat.add(mul_k(nn, mp, at, Word.shl(nn, bb), acc), Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb))),
            M3.pow2(nn))), Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), acc)),
            Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), acc), M3.pow2(nn)), Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), M3.pow2(nn)))), Nat.add(Word.to_nat(nn, acc), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb))), Equal.cong(Nat, Nat, z92 => Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at,
            Word.shl(nn, bb), acc)), z92), Nat.mul(Nat.add(mul_k(nn, mp, at, Word.shl(nn, bb), acc),
            Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb))), M3.pow2(nn)), Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn,
            bb), acc), M3.pow2(nn)), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn))),
            nat_mul_add_r(mul_k(nn, mp, at, Word.shl(nn, bb), acc), Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            M3.pow2(nn))), Equal.trans(Nat, Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), acc)),
            Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), acc), M3.pow2(nn)), Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), M3.pow2(nn)))), Nat.add(Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb),
            acc)), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), acc), M3.pow2(nn))), Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), M3.pow2(nn))), Nat.add(Word.to_nat(nn, acc), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb))), Equal.sym(Nat, Nat.add(Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn,
            bb), acc)), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), acc), M3.pow2(nn))), Nat.mul(Nat.mul(Word.to_nat(mp,
            at), shl_top(nn, bb)), M3.pow2(nn))), Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb),
                acc)),
            Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), acc), M3.pow2(nn)), Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), M3.pow2(nn)))), M3.nat_add_assoc(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb),
            acc)), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), acc), M3.pow2(nn)), Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), M3.pow2(nn)))), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at,
            Word.shl(nn, bb), acc)), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), acc), M3.pow2(nn))),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn))), Nat.add(Nat.add(Word.to_nat(nn, acc),
            Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb)))), Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), M3.pow2(nn))), Nat.add(Word.to_nat(nn, acc), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb))), Equal.cong(Nat, Nat, z93 => Nat.add(z93, Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), M3.pow2(nn))), Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), acc)),
            Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), acc), M3.pow2(nn))), Nat.add(Word.to_nat(nn, acc),
            Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb)))), w_mulgo(nn, mp, at, Word.shl(nn, bb),
            acc)), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb)))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn))),
            Nat.add(Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb)))),
            Nat.mul(Word.to_nat(mp, at), Nat.mul(shl_top(nn, bb), M3.pow2(nn)))), Nat.add(Word.to_nat(nn, acc),
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb))), Equal.cong(Nat, Nat,
            z94 => Nat.add(Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn,
            bb)))), z94), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(Word.to_nat(mp,
            at), Nat.mul(shl_top(nn, bb), M3.pow2(nn))), nat_mul_assoc(Word.to_nat(mp, at), shl_top(nn, bb),
                M3.pow2(nn))),
            Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb)))), Nat.mul(Word.to_nat(mp, at), Nat.mul(shl_top(nn, bb), M3.pow2(nn)))),
            Nat.add(Word.to_nat(nn, acc), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Word.to_nat(mp, at), Nat.mul(shl_top(nn, bb), M3.pow2(nn))))), Nat.add(Word.to_nat(nn, acc),
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb))), M3.nat_add_assoc(Word.to_nat(nn, acc),
            Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Word.to_nat(mp, at),
            Nat.mul(shl_top(nn, bb), M3.pow2(nn)))), Equal.trans(Nat, Nat.add(Word.to_nat(nn, acc),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Word.to_nat(mp, at),
            Nat.mul(shl_top(nn, bb), M3.pow2(nn))))), Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mp, at),
            Nat.add(Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb), M3.pow2(nn))))), Nat.add(Word.to_nat(nn,
            acc), Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb))), Equal.cong(Nat, Nat,
            z95 => Nat.add(Word.to_nat(nn, acc), z95), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb))), Nat.mul(Word.to_nat(mp, at), Nat.mul(shl_top(nn, bb), M3.pow2(nn)))),
            Nat.mul(Word.to_nat(mp, at), Nat.add(Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb),
            M3.pow2(nn)))), Equal.sym(Nat, Nat.mul(Word.to_nat(mp, at), Nat.add(Word.to_nat(nn, Word.shl(nn, bb)),
            Nat.mul(shl_top(nn, bb), M3.pow2(nn)))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn,
            bb))), Nat.mul(Word.to_nat(mp, at), Nat.mul(shl_top(nn, bb), M3.pow2(nn)))), nat_mul_add_l(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb), M3.pow2(nn))))), Equal.trans(Nat,
            Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mp, at), Nat.add(Word.to_nat(nn, Word.shl(nn, bb)),
            Nat.mul(shl_top(nn, bb), M3.pow2(nn))))), Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mp, at),
            Nat.double(Word.to_nat(nn, bb)))), Nat.add(Word.to_nat(nn, acc), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb))), Equal.cong(Nat, Nat, z96 => Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mp,
            at), z96)), Nat.add(Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb), M3.pow2(nn))),
            Nat.double(Word.to_nat(nn, bb)), w_shl(nn, bb)), Equal.trans(Nat, Nat.add(Word.to_nat(nn, acc),
            Nat.mul(Word.to_nat(mp, at), Nat.double(Word.to_nat(nn, bb)))), Nat.add(Word.to_nat(nn, acc),
            Nat.double(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, bb)))), Nat.add(Word.to_nat(nn, acc),
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb))), Equal.cong(Nat, Nat,
            z97 => Nat.add(Word.to_nat(nn, acc), z97), Nat.mul(Word.to_nat(mp, at), Nat.double(Word.to_nat(nn, bb))),
            Nat.double(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, bb))), nat_mul_double_r(Word.to_nat(mp, at),
            Word.to_nat(nn, bb))), Equal.cong(Nat, Nat, z98 => Nat.add(Word.to_nat(nn, acc), z98),
            Nat.double(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, bb))), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb)), Equal.sym(Nat, Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)),
            Nat.double(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, bb))), nat_mul_double_l(Word.to_nat(mp, at),
            Word.to_nat(nn, bb))))))))))))
        case WCon{True{}, +at}:
          Equal.trans(Nat, Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb))),
            Nat.mul(Nat.add(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)), Nat.add(Nat.mul(Word.to_nat(mp,
            at), shl_top(nn, bb)), adc_k(nn, acc, bb, False{}, False{}))), M3.pow2(nn))), Nat.add(Word.to_nat(nn,
            Word.mul.go(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb))), Nat.add(Nat.mul(mul_k(nn, mp, at,
            Word.shl(nn, bb), Word.add(nn, acc, bb)), M3.pow2(nn)), Nat.mul(Nat.add(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), adc_k(nn, acc, bb, False{}, False{})), M3.pow2(nn)))), Nat.add(Word.to_nat(nn, acc),
            Nat.add(Word.to_nat(nn, bb), Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)))),
            Equal.cong(Nat, Nat, z99 => Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), Word.add(nn,
            acc, bb))), z99), Nat.mul(Nat.add(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), adc_k(nn, acc, bb, False{}, False{}))), M3.pow2(nn)),
            Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)), M3.pow2(nn)),
            Nat.mul(Nat.add(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), adc_k(nn, acc, bb, False{}, False{})),
            M3.pow2(nn))), nat_mul_add_r(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), adc_k(nn, acc, bb, False{}, False{})), M3.pow2(nn))),
            Equal.trans(Nat, Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb))),
            Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)), M3.pow2(nn)),
            Nat.mul(Nat.add(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), adc_k(nn, acc, bb, False{}, False{})),
            M3.pow2(nn)))), Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb))),
            Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)), M3.pow2(nn)),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), M3.pow2(nn))))), Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb),
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)))), Equal.cong(Nat, Nat,
            z100 => Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb))),
            Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)), M3.pow2(nn)), z100)),
            Nat.mul(Nat.add(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), adc_k(nn, acc, bb, False{}, False{})),
            M3.pow2(nn)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
                Nat.mul(adc_k(nn, acc,
            bb, False{}, False{}), M3.pow2(nn))), nat_mul_add_r(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), adc_k(nn,
            acc, bb, False{}, False{}), M3.pow2(nn))), Equal.trans(Nat, Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at,
            Word.shl(nn, bb), Word.add(nn, acc, bb))), Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn,
            acc, bb)), M3.pow2(nn)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
            Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn))))), Nat.add(Nat.add(Word.to_nat(nn,
                Word.mul.go(nn,
            mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb))), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn,
            acc, bb)), M3.pow2(nn))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
            Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)))), Nat.add(Word.to_nat(nn, acc),
            Nat.add(Word.to_nat(nn, bb), Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)))),
            Equal.sym(Nat, Nat.add(Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc,
            bb))), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)), M3.pow2(nn))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), M3.pow2(nn)))), Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb),
            Word.add(nn, acc, bb))), Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)),
            M3.pow2(nn)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
                Nat.mul(adc_k(nn, acc,
            bb, False{}, False{}), M3.pow2(nn))))), M3.nat_add_assoc(Word.to_nat(nn, Word.mul.go(nn, mp, at,
                Word.shl(nn,
            bb), Word.add(nn, acc, bb))), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)),
            M3.pow2(nn)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
                Nat.mul(adc_k(nn, acc,
            bb, False{}, False{}), M3.pow2(nn))))), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp,
            at, Word.shl(nn, bb), Word.add(nn, acc, bb))), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn,
            acc, bb)), M3.pow2(nn))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
            Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)))), Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn,
            acc, bb)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb)))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), M3.pow2(nn)))), Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb),
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)))), Equal.cong(Nat, Nat, z101 => Nat.add(z101,
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), M3.pow2(nn)))), Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb),
            Word.add(nn, acc, bb))), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)), M3.pow2(nn))),
            Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn,
            bb)))), w_mulgo(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb))), Equal.trans(Nat,
            Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb)))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
            Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)))), Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn,
            acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn))), Nat.add(Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)))),
            Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb)))), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)),
            Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb)))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp,
            at), shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)),
            Word.to_nat(nn, Word.add(nn, acc, bb))))), Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)),
            Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn))), Nat.add(Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)))),
            Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb)))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            M3.pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)))),
            Nat.add(Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn,
            Word.add(nn, acc, bb))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
            Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), M3.pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)), Word.to_nat(nn, Word.add(nn, acc,
                bb))))),
            Equal.cong(Nat, Nat, z102 => Nat.add(z102, Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            M3.pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)))), Nat.add(Word.to_nat(nn,
                Word.add(nn,
            acc, bb)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb)))),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc,
            bb))), M3.nat_add_comm(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb))))), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc, bb))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)))),
            Nat.add(Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn,
            Word.add(nn, acc, bb))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
            Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), M3.pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)), Word.to_nat(nn, Word.add(nn, acc,
                bb))))),
            Equal.cong(Nat, Nat, z103 => Nat.add(Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn,
            bb))), Word.to_nat(nn, Word.add(nn, acc, bb))), z103), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), M3.pow2(nn))), {==}), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc, bb))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), M3.pow2(nn)))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn,
            bb)), M3.pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn))))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)),
            Word.to_nat(nn, Word.add(nn, acc, bb))))), M3.nat_add_assoc(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)))),
                Equal.trans(Nat,
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Word.to_nat(nn,
            Word.add(nn, acc, bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
            Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn))))), Nat.add(Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            M3.pow2(nn)), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)), Word.to_nat(nn,
                Word.add(nn,
            acc, bb))))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), M3.pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))))), Equal.cong(Nat, Nat,
            z105 => Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), z105),
            Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn,
            bb)), M3.pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.add(Nat.mul(adc_k(nn, acc,
            bb, False{}, False{}), M3.pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb)))), Equal.trans(Nat,
            Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn,
            bb)), M3.pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.add(Word.to_nat(nn,
            Word.add(nn, acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.add(Nat.mul(adc_k(nn, acc,
            bb, False{}, False{}), M3.pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb)))),
                M3.nat_add_lcomm(Word.to_nat(nn,
            Word.add(nn, acc, bb)), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
                Nat.mul(adc_k(nn,
            acc, bb, False{}, False{}), M3.pow2(nn))), Equal.cong(Nat, Nat,
            z104 => Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), z104),
            Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn))),
            Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))),
            M3.nat_add_comm(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}),
            M3.pow2(nn)))))), M3.nat_add_lcomm(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.add(Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), M3.pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb)))))))), Equal.sym(Nat,
            Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}),
            M3.pow2(nn))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)))),
                Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp,
            at), shl_top(nn, bb)), M3.pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn,
                bb))),
            Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)), Word.to_nat(nn, Word.add(nn, acc,
                bb))))),
            Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), M3.pow2(nn))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)))), Nat.add(Nat.add(Nat.mul(adc_k(nn,
                acc,
            bb, False{}, False{}), M3.pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))),
                Nat.add(Nat.mul(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            M3.pow2(nn)))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), M3.pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))))), Equal.cong(Nat, Nat,
            z106 => Nat.add(z106, Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)))), Nat.add(Word.to_nat(nn, Word.add(nn,
            acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn))), Nat.add(Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), M3.pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))), M3.nat_add_comm(Word.to_nat(nn,
            Word.add(nn, acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)))), Equal.trans(Nat,
            Nat.add(Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)), Word.to_nat(nn, Word.add(nn,
                acc,
            bb))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)))), Nat.add(Nat.add(Nat.mul(adc_k(nn,
                acc,
            bb, False{}, False{}), M3.pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            M3.pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)), Word.to_nat(nn, Word.add(nn, acc,
                bb))))),
            Equal.cong(Nat, Nat, z107 => Nat.add(Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)),
            Word.to_nat(nn, Word.add(nn, acc, bb))), z107), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb)))), M3.nat_add_comm(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
                Word.shl(nn,
            bb))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)))), Equal.trans(Nat,
            Nat.add(Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)), Word.to_nat(nn, Word.add(nn,
                acc,
            bb))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb))))), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}),
                M3.pow2(nn)),
            Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn,
            bb)), M3.pow2(nn)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb)))))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)),
            Word.to_nat(nn, Word.add(nn, acc, bb))))), M3.nat_add_assoc(Nat.mul(adc_k(nn, acc, bb, False{}, False{}),
            M3.pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at),
                shl_top(nn,
            bb)), M3.pow2(nn)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))))), Equal.trans(Nat,
            Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)), Nat.add(Word.to_nat(nn, Word.add(nn,
                acc,
            bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb)))))), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}),
            M3.pow2(nn)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc,
            bb))))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), M3.pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))))), Equal.cong(Nat, Nat,
            z109 => Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)), z109), Nat.add(Word.to_nat(nn,
            Word.add(nn, acc, bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
            Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp,
            at), shl_top(nn, bb)), M3.pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn,
                bb))),
            Word.to_nat(nn, Word.add(nn, acc, bb)))), Equal.trans(Nat, Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            M3.pow2(nn)), Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb))))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc,
            bb)))), M3.nat_add_lcomm(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb)))),
            Equal.cong(Nat, Nat, z108 => Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
            z108), Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb)))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Word.to_nat(nn, Word.add(nn, acc, bb))), M3.nat_add_comm(Word.to_nat(nn, Word.add(nn, acc, bb)),
            Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))))))), Equal.trans(Nat,
            Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp,
            at), shl_top(nn, bb)), M3.pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn,
                bb))),
            Word.to_nat(nn, Word.add(nn, acc, bb))))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            M3.pow2(nn)), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)),
                Nat.add(Nat.mul(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc, bb))))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)),
            Word.to_nat(nn, Word.add(nn, acc, bb))))), M3.nat_add_lcomm(Nat.mul(adc_k(nn, acc, bb, False{}, False{}),
            M3.pow2(nn)), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc,
            bb)))), Equal.cong(Nat, Nat, z110 => Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            M3.pow2(nn)), z110), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc,
            bb)))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(adc_k(nn,
            acc, bb, False{}, False{}), M3.pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb)))),
            M3.nat_add_lcomm(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn)), Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc, bb))))))))))), Equal.trans(Nat,
            Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}),
            M3.pow2(nn))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)))), Nat.add(Nat.add(Word.to_nat(nn, acc),
            Nat.add(Word.to_nat(nn, bb), 0n)), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)))), Nat.add(Word.to_nat(nn, acc),
            Nat.add(Word.to_nat(nn, bb), Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)))),
            Equal.cong(Nat, Nat, z111 => Nat.add(z111, Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)))),
            Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), M3.pow2(nn))),
            Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb), 0n)), w_adc(nn, acc, bb, False{}, False{})),
            Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb), 0n)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp,
            at), shl_top(nn, bb)), M3.pow2(nn)))), Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp,
            at), shl_top(nn, bb)), M3.pow2(nn)))), Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb),
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)))), Equal.cong(Nat, Nat,
            z112 => Nat.add(Nat.add(Word.to_nat(nn, acc), z112), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)))),
            Nat.add(Word.to_nat(nn, bb), 0n), Word.to_nat(nn, bb), M3.nat_add_zero(Word.to_nat(nn, bb))),
                Equal.trans(Nat,
            Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)), Nat.add(Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)))),
            Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)), Nat.add(Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Word.to_nat(mp, at), Nat.mul(shl_top(nn, bb), M3.pow2(nn))))),
            Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb)))), Equal.cong(Nat, Nat, z113 => Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn,
            bb)), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), z113)),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), M3.pow2(nn)), Nat.mul(Word.to_nat(mp, at),
            Nat.mul(shl_top(nn, bb), M3.pow2(nn))), nat_mul_assoc(Word.to_nat(mp, at), shl_top(nn, bb), M3.pow2(nn))),
            Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Word.to_nat(mp, at),
            Nat.mul(shl_top(nn, bb), M3.pow2(nn))))), Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)),
            Nat.mul(Word.to_nat(mp, at), Nat.add(Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb),
            M3.pow2(nn))))), Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb),
                Nat.mul(Nat.double(Word.to_nat(mp,
            at)), Word.to_nat(nn, bb)))), Equal.cong(Nat, Nat, z114 => Nat.add(Nat.add(Word.to_nat(nn, acc),
            Word.to_nat(nn, bb)), z114), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Word.to_nat(mp, at), Nat.mul(shl_top(nn, bb), M3.pow2(nn)))), Nat.mul(Word.to_nat(mp, at),
            Nat.add(Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb), M3.pow2(nn)))), Equal.sym(Nat,
            Nat.mul(Word.to_nat(mp, at), Nat.add(Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb),
            M3.pow2(nn)))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Word.to_nat(mp, at), Nat.mul(shl_top(nn, bb), M3.pow2(nn)))), nat_mul_add_l(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb), M3.pow2(nn))))), Equal.trans(Nat,
            Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)), Nat.mul(Word.to_nat(mp, at),
            Nat.add(Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb), M3.pow2(nn))))),
            Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)), Nat.mul(Word.to_nat(mp, at),
            Nat.double(Word.to_nat(nn, bb)))), Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb),
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)))), Equal.cong(Nat, Nat,
            z115 => Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)), Nat.mul(Word.to_nat(mp, at), z115)),
            Nat.add(Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb), M3.pow2(nn))),
                Nat.double(Word.to_nat(nn,
            bb)), w_shl(nn, bb)), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)),
            Nat.mul(Word.to_nat(mp, at), Nat.double(Word.to_nat(nn, bb)))), Nat.add(Nat.add(Word.to_nat(nn, acc),
            Word.to_nat(nn, bb)), Nat.double(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, bb)))),
            Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb)))), Equal.cong(Nat, Nat, z116 => Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn,
            bb)), z116), Nat.mul(Word.to_nat(mp, at), Nat.double(Word.to_nat(nn, bb))),
            Nat.double(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, bb))), nat_mul_double_r(Word.to_nat(mp, at),
            Word.to_nat(nn, bb))), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)),
            Nat.double(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, bb)))), Nat.add(Nat.add(Word.to_nat(nn, acc),
            Word.to_nat(nn, bb)), Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb))),
            Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb)))), Equal.cong(Nat, Nat, z117 => Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn,
            bb)), z117), Nat.double(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, bb))),
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)), Equal.sym(Nat,
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)), Nat.double(Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, bb))), nat_mul_double_l(Word.to_nat(mp, at), Word.to_nat(nn, bb)))),
            M3.nat_add_assoc(Word.to_nat(nn, acc), Word.to_nat(nn, bb), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb)))))))))))))))

# w_mulgo, with 2^nn named through uu
law w_mulgo_u:
  for +nn: Nat
  for uu: Unit
  for mm: Nat
  for aa: Word(mm)
  for +bb: Word(nn)
  for +acc: Word(nn)
  {Nat.add(Word.to_nat(nn, Word.mul.go(nn, mm, aa, bb, acc)), Nat.mul(mul_k(nn, mm, aa, bb, acc), M3.pow2u(nn, uu))) ==
    Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mm, aa), Word.to_nat(nn, bb))) : Nat}

def w_mulgo_u(nn, uu, mm, aa, bb, acc):
  match uu:
    case Unit{}:
      w_mulgo(nn, mm, aa, bb, acc)

# a U32's word
def u32w(uu: U32) -> Word(32n):
  match uu:
    case U32{ww}:
      ww

# how many times 2^32 a U32 times ten passes
def umk(aa: U32) -> Nat:
  match aa:
    case U32{xw}:
      mul_k(32n, 32n, xw, u32w(10), Word.zero(32n))

# a U32 times ten, and how many times it passes 2^32, is the Nat times ten
law u_mul10:
  for +uu: Unit
  for aa: U32
  {Nat.add(U32.to_nat(U32.mul(aa, 10)), Nat.mul(umk(aa), M3.pow2u(32n, uu))) == Nat.mul(U32.to_nat(aa), 10n) : Nat}

def u_mul10(uu, aa):
  match aa:
    case U32{xw}:
      w_mulgo_u(32n, uu, 32n, xw, u32w(10), Word.zero(32n))

# laws/AsU32ReadsPlainDigits.bend: 2^32 is large, a U32 is below it

# 2^nn is one more than something
law p2_pos:
  for +nn: Nat
  {M3.pow2(nn) == 1n+Nat.sub(M3.pow2(nn), 1n) : Nat}

def p2_pos(nn):
  match nn:
    case 0n:
      {==}
    case 1n+(+pp):
      ee = Equal.sym(Nat, M3.pow2(pp), 1n+Nat.sub(M3.pow2(pp), 1n), p2_pos(pp))
      %ee : {Nat.double(_) == 1n+Nat.sub(Nat.double(_), 1n) : Nat}
      {==}

# six doublings
def dbl6(nn: Nat) -> Nat:
  Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(nn))))))

# what 2^(6 + mm) is past 64, once uu is known
def pz6(mm: Nat, uu: Unit) -> Nat:
  match uu:
    case Unit{}:
      dbl6(Nat.sub(M3.pow2(mm), 1n))

# 2^(6 + mm) is 64 and more
law pw_big:
  for +mm: Nat
  for uu: Unit
  {M3.pow2u(6n+mm, uu) == Nat.add(64n, pz6(mm, uu)) : Nat}

def pw_big(mm, uu):
  match uu:
    case Unit{}:
      Equal.cong(Nat, Nat, xx => dbl6(xx), M3.pow2(mm), 1n+Nat.sub(M3.pow2(mm), 1n), p2_pos(mm))

# s + k*t is e + t, both below t: s is e
law nat_mod_one:
  for kk: Nat
  for +ss: Nat
  for +ee: Nat
  for +tt: Nat
  for h: {Nat.add(ss, Nat.mul(kk, tt)) == Nat.add(ee, tt) : Nat}
  for hs: {Nat.is_lt(ss, tt) == True{} : Bool}
  for he: {Nat.is_lt(ee, tt) == True{} : Bool}
  {ss == ee : Nat}

def nat_mod_one(kk, ss, ee, tt, h, hs, he):
  match kk:
    case 0n:
      Empty.absurd({ss == ee : Nat}, M1.true_false(Equal.trans(Bool, True{}, Nat.is_lt(ss, tt), False{}, Equal.sym(Bool,
        Nat.is_lt(ss, tt), True{}, hs), Equal.trans(Bool, Nat.is_lt(ss, tt), Nat.is_lt(Nat.add(ss, 0n), tt), False{},
        Equal.cong(Nat, Bool, z118 => Nat.is_lt(z118, tt), ss, Nat.add(ss, 0n), Equal.sym(Nat, Nat.add(ss, 0n), ss,
        M3.nat_add_zero(ss))), Equal.trans(Bool, Nat.is_lt(Nat.add(ss, 0n), tt), Nat.is_lt(Nat.add(ee, tt), tt),
            False{},
        Equal.cong(Nat, Bool, z119 => Nat.is_lt(z119, tt), Nat.add(ss, 0n), Nat.add(ee, tt), h), Equal.trans(Bool,
        Nat.is_lt(Nat.add(ee, tt), tt), Nat.is_lt(Nat.add(tt, ee), tt), False{}, Equal.cong(Nat, Bool,
        z120 => Nat.is_lt(z120, tt), Nat.add(ee, tt), Nat.add(tt, ee), M3.nat_add_comm(ee, tt)), nat_nlt_add(tt,
            ee)))))))
    case 1n+(+kp):
      nat_mod_small(kp, ss, ee, tt, M3.nat_add_cancel(tt, Nat.add(ss, Nat.mul(kp, tt)), ee, Equal.trans(Nat, Nat.add(tt,
        Nat.add(ss, Nat.mul(kp, tt))), Nat.add(ss, Nat.add(tt, Nat.mul(kp, tt))), Nat.add(tt, ee), Equal.sym(Nat,
        Nat.add(ss, Nat.add(tt, Nat.mul(kp, tt))), Nat.add(tt, Nat.add(ss, Nat.mul(kp, tt))), M3.nat_add_lcomm(ss, tt,
        Nat.mul(kp, tt))), Equal.trans(Nat, Nat.add(ss, Nat.add(tt, Nat.mul(kp, tt))), Nat.add(ee, tt), Nat.add(tt,
        ee), h, M3.nat_add_comm(ee, tt)))), he)

# a U32 difference that does not pass below 0 is the Nat difference
law u_sub_ge:
  for +uu: Unit
  for +aa: U32
  for +bb: U32
  for +h: {Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)) == False{} : Bool}
  {Nat.add(U32.to_nat(U32.sub(aa, bb)), U32.to_nat(bb)) == U32.to_nat(aa) : Nat}

def u_sub_ge(uu, aa, bb, h):
  Equal.trans(Nat, Nat.add(U32.to_nat(U32.sub(aa, bb)), U32.to_nat(bb)), Nat.add(Nat.sub(U32.to_nat(aa),
    U32.to_nat(bb)), U32.to_nat(bb)), U32.to_nat(aa), Equal.cong(Nat, Nat, z126 => Nat.add(z126, U32.to_nat(bb)),
    U32.to_nat(U32.sub(aa, bb)), Nat.sub(U32.to_nat(aa), U32.to_nat(bb)), nat_mod_one(usub_k(aa, bb),
    U32.to_nat(U32.sub(aa, bb)), Nat.sub(U32.to_nat(aa), U32.to_nat(bb)), M3.pow2u(32n, uu),
    M3.nat_add_cancel(U32.to_nat(bb), Nat.add(U32.to_nat(U32.sub(aa, bb)), Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu))),
    Nat.add(Nat.sub(U32.to_nat(aa), U32.to_nat(bb)), M3.pow2u(32n, uu)), Equal.trans(Nat, Nat.add(U32.to_nat(bb),
    Nat.add(U32.to_nat(U32.sub(aa, bb)), Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)))), Nat.add(U32.to_nat(U32.sub(aa,
    bb)), Nat.add(Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)), U32.to_nat(bb))), Nat.add(U32.to_nat(bb),
    Nat.add(Nat.sub(U32.to_nat(aa), U32.to_nat(bb)), M3.pow2u(32n, uu))), Equal.trans(Nat, Nat.add(U32.to_nat(bb),
    Nat.add(U32.to_nat(U32.sub(aa, bb)), Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)))), Nat.add(Nat.mul(usub_k(aa, bb),
    M3.pow2u(32n, uu)), Nat.add(U32.to_nat(U32.sub(aa, bb)), U32.to_nat(bb))), Nat.add(U32.to_nat(U32.sub(aa, bb)),
    Nat.add(Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)), U32.to_nat(bb))), Equal.trans(Nat, Nat.add(U32.to_nat(bb),
    Nat.add(U32.to_nat(U32.sub(aa, bb)), Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)))), Nat.add(U32.to_nat(bb),
    Nat.add(Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)), U32.to_nat(U32.sub(aa, bb)))), Nat.add(Nat.mul(usub_k(aa, bb),
    M3.pow2u(32n, uu)), Nat.add(U32.to_nat(U32.sub(aa, bb)), U32.to_nat(bb))), Equal.cong(Nat, Nat,
    z121 => Nat.add(U32.to_nat(bb), z121), Nat.add(U32.to_nat(U32.sub(aa, bb)), Nat.mul(usub_k(aa, bb), M3.pow2u(32n,
    uu))), Nat.add(Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)), U32.to_nat(U32.sub(aa, bb))),
    M3.nat_add_comm(U32.to_nat(U32.sub(aa, bb)), Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)))), Equal.trans(Nat,
    Nat.add(U32.to_nat(bb), Nat.add(Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)), U32.to_nat(U32.sub(aa, bb)))),
    Nat.add(Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)), Nat.add(U32.to_nat(bb), U32.to_nat(U32.sub(aa, bb)))),
    Nat.add(Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)), Nat.add(U32.to_nat(U32.sub(aa, bb)), U32.to_nat(bb))),
    M3.nat_add_lcomm(U32.to_nat(bb), Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)), U32.to_nat(U32.sub(aa, bb))),
    Equal.cong(Nat, Nat, z122 => Nat.add(Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)), z122), Nat.add(U32.to_nat(bb),
    U32.to_nat(U32.sub(aa, bb))), Nat.add(U32.to_nat(U32.sub(aa, bb)), U32.to_nat(bb)), M3.nat_add_comm(U32.to_nat(bb),
    U32.to_nat(U32.sub(aa, bb)))))), Equal.sym(Nat, Nat.add(U32.to_nat(U32.sub(aa, bb)), Nat.add(Nat.mul(usub_k(aa,
    bb), M3.pow2u(32n, uu)), U32.to_nat(bb))), Nat.add(Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)),
    Nat.add(U32.to_nat(U32.sub(aa, bb)), U32.to_nat(bb))), Equal.trans(Nat, Nat.add(U32.to_nat(U32.sub(aa, bb)),
    Nat.add(Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)), U32.to_nat(bb))), Nat.add(U32.to_nat(U32.sub(aa, bb)),
    Nat.add(Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)), U32.to_nat(bb))), Nat.add(Nat.mul(usub_k(aa, bb), M3.pow2u(32n,
        uu)),
    Nat.add(U32.to_nat(U32.sub(aa, bb)), U32.to_nat(bb))), Equal.cong(Nat, Nat, z123 => Nat.add(U32.to_nat(U32.sub(aa,
    bb)), z123), Nat.add(Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)), U32.to_nat(bb)), Nat.add(Nat.mul(usub_k(aa, bb),
    M3.pow2u(32n, uu)), U32.to_nat(bb)), {==}), M3.nat_add_lcomm(U32.to_nat(U32.sub(aa, bb)), Nat.mul(usub_k(aa, bb),
    M3.pow2u(32n, uu)), U32.to_nat(bb))))), Equal.trans(Nat, Nat.add(U32.to_nat(U32.sub(aa, bb)),
    Nat.add(Nat.mul(usub_k(aa, bb), M3.pow2u(32n, uu)), U32.to_nat(bb))), Nat.add(U32.to_nat(aa), M3.pow2u(32n, uu)),
    Nat.add(U32.to_nat(bb), Nat.add(Nat.sub(U32.to_nat(aa), U32.to_nat(bb)), M3.pow2u(32n, uu))), u_sub(uu, aa, bb),
    Equal.trans(Nat, Nat.add(U32.to_nat(aa), M3.pow2u(32n, uu)), Nat.add(Nat.add(U32.to_nat(bb), Nat.sub(U32.to_nat(aa),
    U32.to_nat(bb))), M3.pow2u(32n, uu)), Nat.add(U32.to_nat(bb), Nat.add(Nat.sub(U32.to_nat(aa), U32.to_nat(bb)),
    M3.pow2u(32n, uu))), Equal.cong(Nat, Nat, z124 => Nat.add(z124, M3.pow2u(32n, uu)), U32.to_nat(aa),
    Nat.add(U32.to_nat(bb), Nat.sub(U32.to_nat(aa), U32.to_nat(bb))), Equal.sym(Nat, Nat.add(U32.to_nat(bb),
    Nat.sub(U32.to_nat(aa), U32.to_nat(bb))), U32.to_nat(aa), nat_ge_ex(U32.to_nat(aa), U32.to_nat(bb), h))),
    M3.nat_add_assoc(U32.to_nat(bb), Nat.sub(U32.to_nat(aa), U32.to_nat(bb)), M3.pow2u(32n, uu)))))), M3.u_bound(uu,
        U32.sub(aa,
    bb)), nat_lt_add_l(U32.to_nat(bb), Nat.sub(U32.to_nat(aa), U32.to_nat(bb)), M3.pow2u(32n, uu), Equal.trans(Bool,
    Nat.is_lt(Nat.add(U32.to_nat(bb), Nat.sub(U32.to_nat(aa), U32.to_nat(bb))), M3.pow2u(32n, uu)),
    Nat.is_lt(U32.to_nat(aa), M3.pow2u(32n, uu)), True{}, Equal.cong(Nat, Bool, z125 => Nat.is_lt(z125, M3.pow2u(32n,
        uu)),
    Nat.add(U32.to_nat(bb), Nat.sub(U32.to_nat(aa), U32.to_nat(bb))), U32.to_nat(aa), nat_ge_ex(U32.to_nat(aa),
    U32.to_nat(bb), h)), M3.u_bound(uu, aa))))), Equal.trans(Nat, Nat.add(Nat.sub(U32.to_nat(aa), U32.to_nat(bb)),
    U32.to_nat(bb)), Nat.add(U32.to_nat(bb), Nat.sub(U32.to_nat(aa), U32.to_nat(bb))), U32.to_nat(aa),
    M3.nat_add_comm(Nat.sub(U32.to_nat(aa), U32.to_nat(bb)), U32.to_nat(bb)), nat_ge_ex(U32.to_nat(aa), U32.to_nat(bb),
    h)))

# s + (k*t + y) is x + t and y is past x: k is 0
law sub_lt_k:
  for kk: Nat
  for +ss: Nat
  for +xx: Nat
  for +yy: Nat
  for +ee: Nat
  for +tt: Nat
  for hk: {Nat.add(ss, Nat.add(Nat.mul(kk, tt), yy)) == Nat.add(xx, tt) : Nat}
  for hy: {1n+Nat.add(xx, ee) == yy : Nat}
  {Nat.add(ss, yy) == Nat.add(xx, tt) : Nat}

def sub_lt_k(kk, ss, xx, yy, ee, tt, hk, hy):
  match kk:
    case 0n:
      hk
    case 1n+(+kp):
      Empty.absurd({Nat.add(ss, yy) == Nat.add(xx, tt) : Nat},
        nat_add_ne(xx, Nat.add(ss, Nat.add(Nat.mul(kp, tt), ee)), Equal.trans(Nat, Nat.add(xx, Nat.add(1n, Nat.add(ss,
          Nat.add(Nat.mul(kp, tt), ee)))), Nat.add(ss, Nat.add(Nat.mul(kp, tt), Nat.add(1n, Nat.add(xx, ee)))), xx,
          Equal.trans(Nat, Nat.add(xx, Nat.add(1n, Nat.add(ss, Nat.add(Nat.mul(kp, tt), ee)))), Nat.add(1n,
          Nat.add(Nat.mul(kp, tt), Nat.add(ee, Nat.add(ss, xx)))), Nat.add(ss, Nat.add(Nat.mul(kp, tt), Nat.add(1n,
          Nat.add(xx, ee)))), Equal.trans(Nat, Nat.add(xx, Nat.add(1n, Nat.add(ss, Nat.add(Nat.mul(kp, tt), ee)))),
          Nat.add(xx, Nat.add(1n, Nat.add(Nat.mul(kp, tt), Nat.add(ee, ss)))), Nat.add(1n, Nat.add(Nat.mul(kp, tt),
          Nat.add(ee, Nat.add(ss, xx)))), Equal.cong(Nat, Nat, z135 => Nat.add(xx, z135), Nat.add(1n, Nat.add(ss,
          Nat.add(Nat.mul(kp, tt), ee))), Nat.add(1n, Nat.add(Nat.mul(kp, tt), Nat.add(ee, ss))), Equal.cong(Nat, Nat,
          z134 => Nat.add(1n, z134), Nat.add(ss, Nat.add(Nat.mul(kp, tt), ee)), Nat.add(Nat.mul(kp, tt), Nat.add(ee,
          ss)), Equal.trans(Nat, Nat.add(ss, Nat.add(Nat.mul(kp, tt), ee)), Nat.add(ss, Nat.add(Nat.mul(kp, tt), ee)),
          Nat.add(Nat.mul(kp, tt), Nat.add(ee, ss)), Equal.cong(Nat, Nat, z132 => Nat.add(ss, z132),
          Nat.add(Nat.mul(kp, tt), ee), Nat.add(Nat.mul(kp, tt), ee), {==}), Equal.trans(Nat, Nat.add(ss,
          Nat.add(Nat.mul(kp, tt), ee)), Nat.add(Nat.mul(kp, tt), Nat.add(ss, ee)), Nat.add(Nat.mul(kp, tt),
          Nat.add(ee, ss)), M3.nat_add_lcomm(ss, Nat.mul(kp, tt), ee), Equal.cong(Nat, Nat, z133 => Nat.add(Nat.mul(kp,
          tt), z133), Nat.add(ss, ee), Nat.add(ee, ss), M3.nat_add_comm(ss, ee)))))), Equal.trans(Nat, Nat.add(xx,
          Nat.add(1n, Nat.add(Nat.mul(kp, tt), Nat.add(ee, ss)))), Nat.add(1n, Nat.add(xx, Nat.add(Nat.mul(kp, tt),
          Nat.add(ee, ss)))), Nat.add(1n, Nat.add(Nat.mul(kp, tt), Nat.add(ee, Nat.add(ss, xx)))), M3.nat_add_lcomm(xx,
          1n, Nat.add(Nat.mul(kp, tt), Nat.add(ee, ss))), Equal.cong(Nat, Nat, z138 => Nat.add(1n, z138), Nat.add(xx,
          Nat.add(Nat.mul(kp, tt), Nat.add(ee, ss))), Nat.add(Nat.mul(kp, tt), Nat.add(ee, Nat.add(ss, xx))),
          Equal.trans(Nat, Nat.add(xx, Nat.add(Nat.mul(kp, tt), Nat.add(ee, ss))), Nat.add(Nat.mul(kp, tt), Nat.add(xx,
          Nat.add(ee, ss))), Nat.add(Nat.mul(kp, tt), Nat.add(ee, Nat.add(ss, xx))), M3.nat_add_lcomm(xx, Nat.mul(kp,
              tt),
          Nat.add(ee, ss)), Equal.cong(Nat, Nat, z137 => Nat.add(Nat.mul(kp, tt), z137), Nat.add(xx, Nat.add(ee, ss)),
          Nat.add(ee, Nat.add(ss, xx)), Equal.trans(Nat, Nat.add(xx, Nat.add(ee, ss)), Nat.add(ee, Nat.add(xx, ss)),
          Nat.add(ee, Nat.add(ss, xx)), M3.nat_add_lcomm(xx, ee, ss), Equal.cong(Nat, Nat, z136 => Nat.add(ee, z136),
          Nat.add(xx, ss), Nat.add(ss, xx), M3.nat_add_comm(xx, ss)))))))), Equal.sym(Nat, Nat.add(ss,
              Nat.add(Nat.mul(kp,
          tt), Nat.add(1n, Nat.add(xx, ee)))), Nat.add(1n, Nat.add(Nat.mul(kp, tt), Nat.add(ee, Nat.add(ss, xx)))),
          Equal.trans(Nat, Nat.add(ss, Nat.add(Nat.mul(kp, tt), Nat.add(1n, Nat.add(xx, ee)))), Nat.add(ss, Nat.add(1n,
          Nat.add(Nat.mul(kp, tt), Nat.add(ee, xx)))), Nat.add(1n, Nat.add(Nat.mul(kp, tt), Nat.add(ee, Nat.add(ss,
          xx)))), Equal.cong(Nat, Nat, z141 => Nat.add(ss, z141), Nat.add(Nat.mul(kp, tt), Nat.add(1n, Nat.add(xx,
          ee))), Nat.add(1n, Nat.add(Nat.mul(kp, tt), Nat.add(ee, xx))), Equal.trans(Nat, Nat.add(Nat.mul(kp, tt),
          Nat.add(1n, Nat.add(xx, ee))), Nat.add(Nat.mul(kp, tt), Nat.add(1n, Nat.add(ee, xx))), Nat.add(1n,
          Nat.add(Nat.mul(kp, tt), Nat.add(ee, xx))), Equal.cong(Nat, Nat, z140 => Nat.add(Nat.mul(kp, tt), z140),
          Nat.add(1n, Nat.add(xx, ee)), Nat.add(1n, Nat.add(ee, xx)), Equal.cong(Nat, Nat, z139 => Nat.add(1n, z139),
          Nat.add(xx, ee), Nat.add(ee, xx), M3.nat_add_comm(xx, ee))), M3.nat_add_lcomm(Nat.mul(kp, tt), 1n, Nat.add(ee,
          xx)))), Equal.trans(Nat, Nat.add(ss, Nat.add(1n, Nat.add(Nat.mul(kp, tt), Nat.add(ee, xx)))), Nat.add(1n,
          Nat.add(ss, Nat.add(Nat.mul(kp, tt), Nat.add(ee, xx)))), Nat.add(1n, Nat.add(Nat.mul(kp, tt), Nat.add(ee,
          Nat.add(ss, xx)))), M3.nat_add_lcomm(ss, 1n, Nat.add(Nat.mul(kp, tt), Nat.add(ee, xx))), Equal.cong(Nat, Nat,
          z143 => Nat.add(1n, z143), Nat.add(ss, Nat.add(Nat.mul(kp, tt), Nat.add(ee, xx))), Nat.add(Nat.mul(kp, tt),
          Nat.add(ee, Nat.add(ss, xx))), Equal.trans(Nat, Nat.add(ss, Nat.add(Nat.mul(kp, tt), Nat.add(ee, xx))),
          Nat.add(Nat.mul(kp, tt), Nat.add(ss, Nat.add(ee, xx))), Nat.add(Nat.mul(kp, tt), Nat.add(ee, Nat.add(ss,
          xx))), M3.nat_add_lcomm(ss, Nat.mul(kp, tt), Nat.add(ee, xx)), Equal.cong(Nat, Nat,
              z142 => Nat.add(Nat.mul(kp,
          tt), z142), Nat.add(ss, Nat.add(ee, xx)), Nat.add(ee, Nat.add(ss, xx)), M3.nat_add_lcomm(ss, ee, xx)))))))),
          Equal.trans(Nat, Nat.add(ss, Nat.add(Nat.mul(kp, tt), Nat.add(1n, Nat.add(xx, ee)))), Nat.add(ss,
          Nat.add(Nat.mul(kp, tt), yy)), xx, Equal.cong(Nat, Nat, z144 => Nat.add(ss, Nat.add(Nat.mul(kp, tt), z144)),
          Nat.add(1n, Nat.add(xx, ee)), yy, hy), M3.nat_add_cancel(tt, Nat.add(ss, Nat.add(Nat.mul(kp, tt), yy)), xx,
          Equal.trans(Nat, Nat.add(tt, Nat.add(ss, Nat.add(Nat.mul(kp, tt), yy))), Nat.add(ss, Nat.add(Nat.add(tt,
          Nat.mul(kp, tt)), yy)), Nat.add(tt, xx), Equal.trans(Nat, Nat.add(tt, Nat.add(ss, Nat.add(Nat.mul(kp, tt),
          yy))), Nat.add(Nat.mul(kp, tt), Nat.add(ss, Nat.add(tt, yy))), Nat.add(ss, Nat.add(Nat.add(tt, Nat.mul(kp,
          tt)), yy)), Equal.trans(Nat, Nat.add(tt, Nat.add(ss, Nat.add(Nat.mul(kp, tt), yy))), Nat.add(tt,
          Nat.add(Nat.mul(kp, tt), Nat.add(ss, yy))), Nat.add(Nat.mul(kp, tt), Nat.add(ss, Nat.add(tt, yy))),
          Equal.cong(Nat, Nat, z128 => Nat.add(tt, z128), Nat.add(ss, Nat.add(Nat.mul(kp, tt), yy)),
          Nat.add(Nat.mul(kp, tt), Nat.add(ss, yy)), Equal.trans(Nat, Nat.add(ss, Nat.add(Nat.mul(kp, tt), yy)),
          Nat.add(ss, Nat.add(Nat.mul(kp, tt), yy)), Nat.add(Nat.mul(kp, tt), Nat.add(ss, yy)), Equal.cong(Nat, Nat,
          z127 => Nat.add(ss, z127), Nat.add(Nat.mul(kp, tt), yy), Nat.add(Nat.mul(kp, tt), yy), {==}),
          M3.nat_add_lcomm(ss, Nat.mul(kp, tt), yy))), Equal.trans(Nat, Nat.add(tt, Nat.add(Nat.mul(kp, tt), Nat.add(ss,
          yy))), Nat.add(Nat.mul(kp, tt), Nat.add(tt, Nat.add(ss, yy))), Nat.add(Nat.mul(kp, tt), Nat.add(ss,
          Nat.add(tt, yy))), M3.nat_add_lcomm(tt, Nat.mul(kp, tt), Nat.add(ss, yy)), Equal.cong(Nat, Nat,
          z129 => Nat.add(Nat.mul(kp, tt), z129), Nat.add(tt, Nat.add(ss, yy)), Nat.add(ss, Nat.add(tt, yy)),
          M3.nat_add_lcomm(tt, ss, yy)))), Equal.sym(Nat, Nat.add(ss, Nat.add(Nat.add(tt, Nat.mul(kp, tt)), yy)),
          Nat.add(Nat.mul(kp, tt), Nat.add(ss, Nat.add(tt, yy))), Equal.trans(Nat, Nat.add(ss, Nat.add(Nat.add(tt,
          Nat.mul(kp, tt)), yy)), Nat.add(ss, Nat.add(Nat.mul(kp, tt), Nat.add(tt, yy))), Nat.add(Nat.mul(kp, tt),
          Nat.add(ss, Nat.add(tt, yy))), Equal.cong(Nat, Nat, z131 => Nat.add(ss, z131), Nat.add(Nat.add(tt,
          Nat.mul(kp, tt)), yy), Nat.add(Nat.mul(kp, tt), Nat.add(tt, yy)), Equal.trans(Nat, Nat.add(Nat.add(tt,
          Nat.mul(kp, tt)), yy), Nat.add(Nat.add(Nat.mul(kp, tt), tt), yy), Nat.add(Nat.mul(kp, tt), Nat.add(tt, yy)),
          Equal.cong(Nat, Nat, z130 => Nat.add(z130, yy), Nat.add(tt, Nat.mul(kp, tt)), Nat.add(Nat.mul(kp, tt), tt),
          M3.nat_add_comm(tt, Nat.mul(kp, tt))), M3.nat_add_assoc(Nat.mul(kp, tt), tt, yy))), M3.nat_add_lcomm(ss,
              Nat.mul(kp,
          tt), Nat.add(tt, yy))))), Equal.trans(Nat, Nat.add(ss, Nat.add(Nat.add(tt, Nat.mul(kp, tt)), yy)),
          Nat.add(xx, tt), Nat.add(tt, xx), hk, M3.nat_add_comm(xx, tt))))))))

# a U32 difference that passes below 0 wraps around by 2^32
law u_sub_lt:
  for +uu: Unit
  for +aa: U32
  for +bb: U32
  for h: {Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)) == True{} : Bool}
  {Nat.add(U32.to_nat(U32.sub(aa, bb)), U32.to_nat(bb)) == Nat.add(U32.to_nat(aa), M3.pow2u(32n, uu)) : Nat}

def u_sub_lt(uu, aa, bb, h):
  sub_lt_k(usub_k(aa, bb), U32.to_nat(U32.sub(aa, bb)), U32.to_nat(aa), U32.to_nat(bb),
    Nat.sub(U32.to_nat(bb), 1n+U32.to_nat(aa)), M3.pow2u(32n, uu), u_sub(uu, aa, bb),
    M3.nat_lt_ex(U32.to_nat(aa), U32.to_nat(bb), h))

# laws/AsU32ReadsPlainDigits.bend: U32 division by ten as Nat division

# a Cmp at least EQ is not LT
law cmp_ge_nlt:
  for cc: Cmp
  for h: {Cmp.is_ge(cc) == True{} : Bool}
  {Cmp.is_lt(cc) == False{} : Bool}

def cmp_ge_nlt(cc, h):
  match cc:
    case LT{}:
      Empty.absurd({True{} == False{} : Bool}, M2.false_true(h))
    case EQ{}:
      {==}
    case GT{}:
      {==}

# a Cmp below EQ is LT
law cmp_nge_lt:
  for cc: Cmp
  for h: {Cmp.is_ge(cc) == False{} : Bool}
  {Cmp.is_lt(cc) == True{} : Bool}

def cmp_nge_lt(cc, h):
  match cc:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({False{} == True{} : Bool}, M1.true_false(h))
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, M1.true_false(h))

# the bit shl.out shifts out
def so_hi(nn: Nat, pr: Bool & Word(nn)) -> Bool:
  (hi, _ww) = pr
  hi

# the word shl.out leaves
def so_w(nn: Nat, pr: Bool & Word(nn)) -> Word(nn):
  (_hi, ww) = pr
  ww

# shl.out's cell, from a shift not yet known
law sho_eta:
  for pp: Nat
  for cc: Bool
  for rr: Bool & Word(pp)
  {Word.shl.out.con(pp, cc, rr) == (so_hi(pp, rr), WCon{cc, so_w(pp, rr)}) : Bool & Word(1n+pp)}

def sho_eta(_pp, _cc, rr):
  (_hi, _ww) = rr
  {==}

# shl.out as Nats: c and twice w, less the bit shifted out
law w_sho:
  for +nn: Nat
  for ww: Word(nn)
  for +cc: Bool
  {Nat.add(Word.to_nat(nn, so_w(nn, Word.shl.out(nn, cc, ww))), Nat.mul(bit_nat(so_hi(nn, Word.shl.out(nn, cc, ww))),
    M3.pow2(nn))) == Nat.add(bit_nat(cc), Nat.double(Word.to_nat(nn, ww))) : Nat}

def w_sho(nn, ww, cc):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          Equal.trans(Nat, Nat.mul(bit_nat(cc), 1n), bit_nat(cc), Nat.add(bit_nat(cc), 0n), nat_mul_one(bit_nat(cc)),
            Equal.sym(Nat, Nat.add(bit_nat(cc), 0n), bit_nat(cc), M3.nat_add_zero(bit_nat(cc))))
    case 1n+(+pp):
      match ww:
        case WCon{+bb, +tt}:
          ee = Equal.sym(Bool & Word(1n+pp), Word.shl.out.con(pp, cc, Word.shl.out(pp, bb, tt)),
            (so_hi(pp, Word.shl.out(pp, bb, tt)), WCon{cc, so_w(pp, Word.shl.out(pp, bb, tt))}), sho_eta(pp, cc,
              Word.shl.out(pp, bb, tt)))
          %ee : {Nat.add(Word.to_nat(1n+pp, so_w(1n+pp, _)), Nat.mul(bit_nat(so_hi(1n+pp, _)),
              Nat.double(M3.pow2(pp)))) ==
            Nat.add(bit_nat(cc), Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))) : Nat}
          Equal.trans(Nat, Nat.add(Word.to_nat(1n+pp, WCon{cc, so_w(pp, Word.shl.out(pp, bb, tt))}),
            Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), Nat.double(M3.pow2(pp)))),
                Nat.add(Nat.add(bit_nat(cc),
            Nat.double(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))))), Nat.mul(bit_nat(so_hi(pp,
            Word.shl.out(pp, bb, tt))), Nat.double(M3.pow2(pp)))), Nat.add(bit_nat(cc), Nat.double(Word.to_nat(1n+pp,
            WCon{bb, tt}))), Equal.cong(Nat, Nat, z145 => Nat.add(z145, Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb,
            tt))), Nat.double(M3.pow2(pp)))), Word.to_nat(1n+pp, WCon{cc, so_w(pp, Word.shl.out(pp, bb, tt))}),
            Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))))), w_nat_con(pp, cc,
            so_w(pp, Word.shl.out(pp, bb, tt)))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(cc),
            Nat.double(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))))), Nat.mul(bit_nat(so_hi(pp,
            Word.shl.out(pp, bb, tt))), Nat.double(M3.pow2(pp)))), Nat.add(Nat.add(bit_nat(cc),
                Nat.double(Word.to_nat(pp,
            so_w(pp, Word.shl.out(pp, bb, tt))))), Nat.double(Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))),
            M3.pow2(pp)))), Nat.add(bit_nat(cc), Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))), Equal.cong(Nat, Nat,
            z146 => Nat.add(Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))))),
            z146), Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), Nat.double(M3.pow2(pp))),
            Nat.double(Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), M3.pow2(pp))),
            nat_mul_double_r(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), M3.pow2(pp))), Equal.trans(Nat,
            Nat.add(Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))))),
            Nat.double(Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), M3.pow2(pp)))), Nat.add(bit_nat(cc),
            Nat.add(Nat.double(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt)))),
            Nat.double(Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), M3.pow2(pp))))), Nat.add(bit_nat(cc),
            Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))), M3.nat_add_assoc(bit_nat(cc), Nat.double(Word.to_nat(pp,
            so_w(pp, Word.shl.out(pp, bb, tt)))), Nat.double(Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))),
            M3.pow2(pp)))), Equal.trans(Nat, Nat.add(bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, so_w(pp,
            Word.shl.out(pp, bb, tt)))), Nat.double(Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))),
                M3.pow2(pp))))),
            Nat.add(bit_nat(cc), Nat.double(Nat.add(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))),
            Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), M3.pow2(pp))))), Nat.add(bit_nat(cc),
            Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))), Equal.cong(Nat, Nat, z147 => Nat.add(bit_nat(cc), z147),
            Nat.add(Nat.double(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt)))),
            Nat.double(Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), M3.pow2(pp)))),
            Nat.double(Nat.add(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))), Nat.mul(bit_nat(so_hi(pp,
            Word.shl.out(pp, bb, tt))), M3.pow2(pp)))), Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(pp, so_w(pp,
            Word.shl.out(pp, bb, tt))), Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), M3.pow2(pp)))),
            Nat.add(Nat.double(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt)))),
            Nat.double(Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), M3.pow2(pp)))),
            M3.nat_double_add(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))), Nat.mul(bit_nat(so_hi(pp,
            Word.shl.out(pp, bb, tt))), M3.pow2(pp))))), Equal.trans(Nat, Nat.add(bit_nat(cc),
            Nat.double(Nat.add(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))), Nat.mul(bit_nat(so_hi(pp,
            Word.shl.out(pp, bb, tt))), M3.pow2(pp))))), Nat.add(bit_nat(cc), Nat.double(Nat.add(bit_nat(bb),
            Nat.double(Word.to_nat(pp, tt))))), Nat.add(bit_nat(cc), Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))),
            Equal.cong(Nat, Nat, z148 => Nat.add(bit_nat(cc), Nat.double(z148)), Nat.add(Word.to_nat(pp, so_w(pp,
            Word.shl.out(pp, bb, tt))), Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), M3.pow2(pp))),
            Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, tt))), w_sho(pp, tt, bb)), Equal.cong(Nat, Nat,
            z149 => Nat.add(bit_nat(cc), Nat.double(z149)), Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, tt))),
            Word.to_nat(1n+pp, WCon{bb, tt}), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{bb, tt}), Nat.add(bit_nat(bb),
            Nat.double(Word.to_nat(pp, tt))), w_nat_con(pp, bb, tt))))))))

# w_sho, with 2^nn named through uu
law w_sho_u:
  for +nn: Nat
  for uu: Unit
  for ww: Word(nn)
  for +cc: Bool
  {Nat.add(Word.to_nat(nn, so_w(nn, Word.shl.out(nn, cc, ww))), Nat.mul(bit_nat(so_hi(nn, Word.shl.out(nn, cc, ww))),
    M3.pow2u(nn, uu))) == Nat.add(bit_nat(cc), Nat.double(Word.to_nat(nn, ww))) : Nat}

def w_sho_u(nn, uu, ww, cc):
  match uu:
    case Unit{}:
      w_sho(nn, ww, cc)

# a quotient from divmod.go
def dmq(mm: Nat, pr: Word(mm) & U32) -> Word(mm):
  (qq, _rr) = pr
  qq

# a remainder from divmod.go
def dmr(mm: Nat, pr: Word(mm) & U32) -> U32:
  (_qq, rr) = pr
  rr

# below y, a bit and twice x is below twice y
law nat_lt_bd:
  for bb: Bool
  for +xx: Nat
  for +yy: Nat
  for h: {Nat.is_lt(xx, yy) == True{} : Bool}
  {Nat.is_lt(Nat.add(bit_nat(bb), Nat.double(xx)), Nat.double(yy)) == True{} : Bool}

def nat_lt_bd(bb, xx, yy, h):
  match bb:
    case False{}:
      M3.nat_lt_dbl(xx, yy, h)
    case True{}:
      M3.nat_lt_dbl1(xx, yy, h)

# below c, the left addend of a sum below c is below c too
law nat_lt_add_rl:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  for h: {Nat.is_lt(Nat.add(aa, bb), cc) == True{} : Bool}
  {Nat.is_lt(aa, cc) == True{} : Bool}

def nat_lt_add_rl(aa, bb, cc, h):
  nat_lt_add_l(bb, aa, cc, Equal.trans(Bool, Nat.is_lt(Nat.add(bb, aa), cc), Nat.is_lt(Nat.add(aa, bb), cc), True{},
    Equal.cong(Nat, Bool, xx => Nat.is_lt(xx, cc), Nat.add(bb, aa), Nat.add(aa, bb), M3.nat_add_comm(bb, aa)), h))

# the last step of divmod.go: the new remainder is below ten
law dm_fin_b:
  for +uu: Unit
  for pp: Nat
  for qq: Word(pp)
  for +ss: Word(32n)
  for gg: Bool
  for eg: {U32.is_ge(U32{ss}, 10) == gg : Bool}
  for hs: {Nat.is_lt(Word.to_nat(32n, ss), 20n) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(dmr(1n+pp, U32.divmod.go.fin(pp, qq, U32{ss}, 10, gg))), 10n) == True{} : Bool}

def dm_fin_b(uu, _pp, _qq, ss, gg, eg, hs):
  match gg:
    case True{}:
      Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32.sub(U32{ss}, 10)), 10n), Nat.is_lt(Nat.add(U32.to_nat(U32.sub(U32{ss},
        10)), 10n), 20n), True{}, Equal.cong(Nat, Bool, z152 => Nat.is_lt(z152, 20n), Nat.add(10n,
        U32.to_nat(U32.sub(U32{ss}, 10))), Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)), 10n), M3.nat_add_comm(10n,
        U32.to_nat(U32.sub(U32{ss}, 10)))), Equal.trans(Bool, Nat.is_lt(Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)), 10n),
        20n), Nat.is_lt(Word.to_nat(32n, ss), 20n), True{}, Equal.cong(Nat, Bool, z153 => Nat.is_lt(z153, 20n),
        Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)), 10n), Word.to_nat(32n, ss), u_sub_ge(uu, U32{ss}, 10,
        cmp_ge_nlt(Nat.cmp(Word.to_nat(32n, ss), 10n), Equal.trans(Bool, Cmp.is_ge(Nat.cmp(Word.to_nat(32n, ss), 10n)),
        Cmp.is_ge(U32.cmp(U32{ss}, 10)), True{}, Equal.cong(Cmp, Bool, z150 => Cmp.is_ge(z150),
        Nat.cmp(Word.to_nat(32n, ss), 10n), U32.cmp(U32{ss}, 10), Equal.sym(Cmp, U32.cmp(U32{ss}, 10),
        Nat.cmp(Word.to_nat(32n, ss), 10n), u_cmp(U32{ss}, 10))), eg)))), hs))
    case False{}:
      cmp_nge_lt(Nat.cmp(Word.to_nat(32n, ss), 10n), Equal.trans(Bool, Cmp.is_ge(Nat.cmp(Word.to_nat(32n, ss), 10n)),
        Cmp.is_ge(U32.cmp(U32{ss}, 10)), False{}, Equal.cong(Cmp, Bool, z151 => Cmp.is_ge(z151),
        Nat.cmp(Word.to_nat(32n, ss), 10n), U32.cmp(U32{ss}, 10), Equal.sym(Cmp, U32.cmp(U32{ss}, 10),
        Nat.cmp(Word.to_nat(32n, ss), 10n), u_cmp(U32{ss}, 10))), eg))

# the last step of divmod.go: ten times the new quotient and the new
# remainder are twenty times the quotient and what was shifted in
law dm_fin_e:
  for +uu: Unit
  for +pp: Nat
  for +qq: Word(pp)
  for +ss: Word(32n)
  for gg: Bool
  for eg: {U32.is_ge(U32{ss}, 10) == gg : Bool}
  for hs: {Nat.is_lt(Word.to_nat(32n, ss), 20n) == True{} : Bool}
  {Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.fin(pp, qq, U32{ss}, 10, gg))), 10n),
    U32.to_nat(dmr(1n+pp, U32.divmod.go.fin(pp, qq, U32{ss}, 10, gg)))) ==
    Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Word.to_nat(32n, ss)) : Nat}

def dm_fin_e(uu, pp, qq, ss, gg, eg, _hs):
  match gg:
    case True{}:
      Equal.trans(Nat, Nat.add(Nat.add(10n, Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n)), U32.to_nat(U32.sub(U32{ss},
        10))), Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)), 10n)),
        Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Word.to_nat(32n, ss)), Equal.trans(Nat,
        Nat.add(Nat.add(10n, Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n)), U32.to_nat(U32.sub(U32{ss}, 10))),
        Nat.add(10n, Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), U32.to_nat(U32.sub(U32{ss}, 10)))),
        Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)), 10n)),
        Equal.trans(Nat, Nat.add(Nat.add(10n, Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n)),
        U32.to_nat(U32.sub(U32{ss}, 10))), Nat.add(Nat.add(10n, Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n)),
        U32.to_nat(U32.sub(U32{ss}, 10))), Nat.add(10n, Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n),
        U32.to_nat(U32.sub(U32{ss}, 10)))), Equal.cong(Nat, Nat, z154 => Nat.add(z154, U32.to_nat(U32.sub(U32{ss},
        10))), Nat.add(10n, Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n)), Nat.add(10n,
        Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n)), {==}), M3.nat_add_assoc(10n, Nat.mul(Nat.double(Word.to_nat(pp,
        qq)), 10n), U32.to_nat(U32.sub(U32{ss}, 10)))), Equal.sym(Nat, Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)),
        10n), Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)), 10n)), Nat.add(10n, Nat.add(Nat.mul(Nat.double(Word.to_nat(pp,
        qq)), 10n), U32.to_nat(U32.sub(U32{ss}, 10)))), Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(Word.to_nat(pp,
        qq)), 10n), Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)), 10n)), Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)),
        10n), Nat.add(10n, U32.to_nat(U32.sub(U32{ss}, 10)))), Nat.add(10n, Nat.add(Nat.mul(Nat.double(Word.to_nat(pp,
        qq)), 10n), U32.to_nat(U32.sub(U32{ss}, 10)))), Equal.cong(Nat, Nat,
        z155 => Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), z155), Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)),
        10n), Nat.add(10n, U32.to_nat(U32.sub(U32{ss}, 10))), M3.nat_add_comm(U32.to_nat(U32.sub(U32{ss}, 10)), 10n)),
        M3.nat_add_lcomm(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), 10n, U32.to_nat(U32.sub(U32{ss}, 10)))))),
        Equal.cong(Nat, Nat, z156 => Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), z156),
        Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)), 10n), Word.to_nat(32n, ss), u_sub_ge(uu, U32{ss}, 10,
        cmp_ge_nlt(Nat.cmp(Word.to_nat(32n, ss), 10n), Equal.trans(Bool, Cmp.is_ge(Nat.cmp(Word.to_nat(32n, ss), 10n)),
        Cmp.is_ge(U32.cmp(U32{ss}, 10)), True{}, Equal.cong(Cmp, Bool, z150 => Cmp.is_ge(z150),
        Nat.cmp(Word.to_nat(32n, ss), 10n), U32.cmp(U32{ss}, 10), Equal.sym(Cmp, U32.cmp(U32{ss}, 10),
        Nat.cmp(Word.to_nat(32n, ss), 10n), u_cmp(U32{ss}, 10))), eg)))))
    case False{}:
      {==}

# divmod.go's shift, when it shifts out 0: the remainder is below ten
law dm_ts2_b:
  for +uu: Unit
  for +pp: Nat
  for +qq: Word(pp)
  for tt: Bool
  for +ss: Word(32n)
  for ht: {tt == False{} : Bool}
  for hs: {Nat.is_lt(Word.to_nat(32n, ss), 20n) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(dmr(1n+pp, U32.divmod.go.shl(pp, qq, 10, (tt, ss)))), 10n) == True{} : Bool}

def dm_ts2_b(uu, pp, qq, tt, ss, ht, hs):
  match tt:
    case False{}:
      dm_fin_b(uu, pp, qq, ss, U32.is_ge(U32{ss}, 10), {==}, hs)
    case True{}:
      Empty.absurd({Nat.is_lt(U32.to_nat(dmr(1n+pp, U32.divmod.go.shl(pp, qq, 10, (True{}, ss)))),
        10n) == True{} : Bool},
        M1.true_false(ht))

# divmod.go's shift, when it shifts out 0: ten times the quotient and the
# remainder
law dm_ts2_e:
  for +uu: Unit
  for +pp: Nat
  for +qq: Word(pp)
  for tt: Bool
  for +ss: Word(32n)
  for ht: {tt == False{} : Bool}
  for hs: {Nat.is_lt(Word.to_nat(32n, ss), 20n) == True{} : Bool}
  {Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.shl(pp, qq, 10, (tt, ss)))), 10n), U32.to_nat(dmr(1n+pp,
    U32.divmod.go.shl(pp, qq, 10, (tt, ss))))) ==
    Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Word.to_nat(32n, ss)) : Nat}

def dm_ts2_e(uu, pp, qq, tt, ss, ht, hs):
  match tt:
    case False{}:
      dm_fin_e(uu, pp, qq, ss, U32.is_ge(U32{ss}, 10), {==}, hs)
    case True{}:
      Empty.absurd({Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.shl(pp, qq, 10, (True{}, ss)))), 10n),
        U32.to_nat(dmr(1n+pp, U32.divmod.go.shl(pp, qq, 10, (True{}, ss))))) ==
        Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Word.to_nat(32n, ss)) : Nat}, M1.true_false(ht))

law dm_ts_b:
  for +uu: Unit
  for +pp: Nat
  for +qq: Word(pp)
  for ts: Bool & Word(32n)
  for ht: {so_hi(32n, ts) == False{} : Bool}
  for hs: {Nat.is_lt(Word.to_nat(32n, so_w(32n, ts)), 20n) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(dmr(1n+pp, U32.divmod.go.shl(pp, qq, 10, ts))), 10n) == True{} : Bool}

def dm_ts_b(uu, pp, qq, ts, ht, hs):
  (tt, ss) = ts
  dm_ts2_b(uu, pp, qq, tt, ss, ht, hs)

law dm_ts_e:
  for +uu: Unit
  for +pp: Nat
  for +qq: Word(pp)
  for ts: Bool & Word(32n)
  for ht: {so_hi(32n, ts) == False{} : Bool}
  for hs: {Nat.is_lt(Word.to_nat(32n, so_w(32n, ts)), 20n) == True{} : Bool}
  {Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.shl(pp, qq, 10, ts))), 10n), U32.to_nat(dmr(1n+pp,
    U32.divmod.go.shl(pp, qq, 10, ts)))) ==
    Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Word.to_nat(32n, so_w(32n, ts))) : Nat}

def dm_ts_e(uu, pp, qq, ts, ht, hs):
  (tt, ss) = ts
  dm_ts2_e(uu, pp, qq, tt, ss, ht, hs)

# the bit shifted out of a remainder below ten is 0: past it, 2^32 is too
# large for the sum to be below twenty
law hi_false:
  for +uu: Unit
  for hb: Bool
  for +ww: Nat
  for +vv: Nat
  for h: {Nat.add(ww, Nat.mul(bit_nat(hb), M3.pow2u(32n, uu))) == vv : Nat}
  for hv: {Nat.is_lt(vv, 20n) == True{} : Bool}
  {hb == False{} : Bool}

def hi_false(uu, hb, ww, vv, h, hv):
  match hb:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, M1.true_false(Equal.trans(Bool, True{}, Nat.is_lt(vv, 20n),
        Nat.is_lt(Nat.add(Nat.add(Nat.add(64n, pz6(26n, uu)), 0n), ww), 20n), Equal.sym(Bool, Nat.is_lt(vv, 20n),
        True{}, hv), Equal.trans(Bool, Nat.is_lt(vv, 20n), Nat.is_lt(Nat.add(ww, Nat.add(M3.pow2u(32n, uu), 0n)), 20n),
        Nat.is_lt(Nat.add(Nat.add(Nat.add(64n, pz6(26n, uu)), 0n), ww), 20n), Equal.cong(Nat, Bool,
        z157 => Nat.is_lt(z157, 20n), vv, Nat.add(ww, Nat.add(M3.pow2u(32n, uu), 0n)), Equal.sym(Nat, Nat.add(ww,
        Nat.add(M3.pow2u(32n, uu), 0n)), vv, h)), Equal.trans(Bool, Nat.is_lt(Nat.add(ww, Nat.add(M3.pow2u(32n, uu),
            0n)),
        20n), Nat.is_lt(Nat.add(Nat.add(M3.pow2u(32n, uu), 0n), ww), 20n), Nat.is_lt(Nat.add(Nat.add(Nat.add(64n,
            pz6(26n,
        uu)), 0n), ww), 20n), Equal.cong(Nat, Bool, z158 => Nat.is_lt(z158, 20n), Nat.add(ww, Nat.add(M3.pow2u(32n, uu),
        0n)), Nat.add(Nat.add(M3.pow2u(32n, uu), 0n), ww), M3.nat_add_comm(ww, Nat.add(M3.pow2u(32n, uu), 0n))),
            Equal.cong(Nat,
        Bool, z159 => Nat.is_lt(Nat.add(Nat.add(z159, 0n), ww), 20n), M3.pow2u(32n, uu), Nat.add(64n, pz6(26n, uu)),
        pw_big(26n, uu)))))))

# one step of divmod.go on a remainder below ten: the new remainder is below
# ten
law dm_rec_b:
  for +uu: Unit
  for +pp: Nat
  for +a0: Bool
  for +qq: Word(pp)
  for +rw: Word(32n)
  for +hr: {Nat.is_lt(Word.to_nat(32n, rw), 10n) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(dmr(1n+pp, U32.divmod.go.rec(pp, a0, 10, (qq, U32{rw})))), 10n) == True{} : Bool}

def dm_rec_b(uu, pp, a0, qq, rw, hr):
  dm_ts_b(uu, pp, qq, Word.shl.out(32n, a0, rw), hi_false(uu, so_hi(32n, Word.shl.out(32n, a0, rw)), Word.to_nat(32n,
    so_w(32n, Word.shl.out(32n, a0, rw))), Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw))), w_sho_u(32n, uu, rw,
    a0), nat_lt_bd(a0, Word.to_nat(32n, rw), 10n, hr)), nat_lt_add_rl(Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0,
    rw))), Nat.mul(bit_nat(so_hi(32n, Word.shl.out(32n, a0, rw))), M3.pow2u(32n, uu)), 20n, Equal.trans(Bool,
    Nat.is_lt(Nat.add(Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw))), Nat.mul(bit_nat(so_hi(32n,
    Word.shl.out(32n, a0, rw))), M3.pow2u(32n, uu))), 20n), Nat.is_lt(Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n,
    rw))), 20n), True{}, Equal.cong(Nat, Bool, z160 => Nat.is_lt(z160, 20n), Nat.add(Word.to_nat(32n, so_w(32n,
    Word.shl.out(32n, a0, rw))), Nat.mul(bit_nat(so_hi(32n, Word.shl.out(32n, a0, rw))), M3.pow2u(32n, uu))),
    Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw))), w_sho_u(32n, uu, rw, a0)), nat_lt_bd(a0, Word.to_nat(32n,
    rw), 10n, hr))))

# one step of divmod.go on a remainder below ten: ten times the quotient and
# the remainder take in one more bit
law dm_rec_e:
  for +uu: Unit
  for +pp: Nat
  for +a0: Bool
  for +qq: Word(pp)
  for +rw: Word(32n)
  for +hr: {Nat.is_lt(Word.to_nat(32n, rw), 10n) == True{} : Bool}
  {Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.rec(pp, a0, 10, (qq, U32{rw})))), 10n),
    U32.to_nat(dmr(1n+pp, U32.divmod.go.rec(pp, a0, 10, (qq, U32{rw}))))) == Nat.add(bit_nat(a0),
    Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, qq), 10n), Word.to_nat(32n, rw)))) : Nat}

def dm_rec_e(uu, pp, a0, qq, rw, hr):
  Equal.trans(Nat, Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.rec(pp, a0, 10, (qq, U32{rw})))), 10n),
    U32.to_nat(dmr(1n+pp, U32.divmod.go.rec(pp, a0, 10, (qq, U32{rw}))))), Nat.add(Nat.mul(Nat.double(Word.to_nat(pp,
    qq)), 10n), Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw)))), Nat.add(bit_nat(a0),
    Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, qq), 10n), Word.to_nat(32n, rw)))), dm_ts_e(uu, pp, qq,
    Word.shl.out(32n, a0, rw), hi_false(uu, so_hi(32n, Word.shl.out(32n, a0, rw)), Word.to_nat(32n, so_w(32n,
    Word.shl.out(32n, a0, rw))), Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw))), w_sho_u(32n, uu, rw, a0),
    nat_lt_bd(a0, Word.to_nat(32n, rw), 10n, hr)), nat_lt_add_rl(Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0,
    rw))), Nat.mul(bit_nat(so_hi(32n, Word.shl.out(32n, a0, rw))), M3.pow2u(32n, uu)), 20n, Equal.trans(Bool,
    Nat.is_lt(Nat.add(Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw))), Nat.mul(bit_nat(so_hi(32n,
    Word.shl.out(32n, a0, rw))), M3.pow2u(32n, uu))), 20n), Nat.is_lt(Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n,
    rw))), 20n), True{}, Equal.cong(Nat, Bool, z160 => Nat.is_lt(z160, 20n), Nat.add(Word.to_nat(32n, so_w(32n,
    Word.shl.out(32n, a0, rw))), Nat.mul(bit_nat(so_hi(32n, Word.shl.out(32n, a0, rw))), M3.pow2u(32n, uu))),
    Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw))), w_sho_u(32n, uu, rw, a0)), nat_lt_bd(a0, Word.to_nat(32n,
    rw), 10n, hr)))), Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Word.to_nat(32n,
    so_w(32n, Word.shl.out(32n, a0, rw)))), Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Nat.add(bit_nat(a0),
    Nat.double(Word.to_nat(32n, rw)))), Nat.add(bit_nat(a0), Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, qq), 10n),
    Word.to_nat(32n, rw)))), Equal.cong(Nat, Nat, z162 => Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), z162),
    Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw))), Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw))),
    Equal.trans(Nat, Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw))), Nat.add(Word.to_nat(32n, so_w(32n,
    Word.shl.out(32n, a0, rw))), 0n), Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw))), Equal.sym(Nat,
    Nat.add(Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw))), 0n), Word.to_nat(32n, so_w(32n, Word.shl.out(32n,
    a0, rw))), M3.nat_add_zero(Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw))))), Equal.trans(Nat,
    Nat.add(Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw))), 0n), Nat.add(Word.to_nat(32n, so_w(32n,
    Word.shl.out(32n, a0, rw))), Nat.mul(bit_nat(so_hi(32n, Word.shl.out(32n, a0, rw))), M3.pow2u(32n, uu))),
    Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw))), Equal.cong(Bool, Nat, z161 => Nat.add(Word.to_nat(32n,
    so_w(32n, Word.shl.out(32n, a0, rw))), Nat.mul(bit_nat(z161), M3.pow2u(32n, uu))), False{}, so_hi(32n,
    Word.shl.out(32n, a0, rw)), Equal.sym(Bool, so_hi(32n, Word.shl.out(32n, a0, rw)), False{}, hi_false(uu, so_hi(32n,
    Word.shl.out(32n, a0, rw)), Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw))), Nat.add(bit_nat(a0),
    Nat.double(Word.to_nat(32n, rw))), w_sho_u(32n, uu, rw, a0), nat_lt_bd(a0, Word.to_nat(32n, rw), 10n, hr)))),
    w_sho_u(32n, uu, rw, a0)))), Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n),
    Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw)))), Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)),
    Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw)))), Nat.add(bit_nat(a0),
    Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, qq), 10n), Word.to_nat(32n, rw)))), Equal.cong(Nat, Nat,
    z163 => Nat.add(z163, Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw)))), Nat.mul(Nat.double(Word.to_nat(pp,
    qq)), 10n), Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), nat_mul_double_l(Word.to_nat(pp, qq), 10n)),
    Equal.trans(Nat, Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.add(bit_nat(a0),
    Nat.double(Word.to_nat(32n, rw)))), Nat.add(bit_nat(a0), Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)),
    Nat.double(Word.to_nat(32n, rw)))), Nat.add(bit_nat(a0), Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, qq), 10n),
    Word.to_nat(32n, rw)))), Equal.trans(Nat, Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)),
    Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw)))), Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)),
    Nat.add(Nat.double(Word.to_nat(32n, rw)), bit_nat(a0))), Nat.add(bit_nat(a0),
    Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.double(Word.to_nat(32n, rw)))), Equal.cong(Nat, Nat,
    z164 => Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), z164), Nat.add(bit_nat(a0),
    Nat.double(Word.to_nat(32n, rw))), Nat.add(Nat.double(Word.to_nat(32n, rw)), bit_nat(a0)),
    M3.nat_add_comm(bit_nat(a0), Nat.double(Word.to_nat(32n, rw)))), Equal.sym(Nat, Nat.add(bit_nat(a0),
    Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.double(Word.to_nat(32n, rw)))),
    Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.add(Nat.double(Word.to_nat(32n, rw)), bit_nat(a0))),
    Equal.trans(Nat, Nat.add(bit_nat(a0), Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)),
    Nat.double(Word.to_nat(32n, rw)))), Nat.add(bit_nat(a0), Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)),
    Nat.double(Word.to_nat(32n, rw)))), Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)),
    Nat.add(Nat.double(Word.to_nat(32n, rw)), bit_nat(a0))), Equal.cong(Nat, Nat, z165 => Nat.add(bit_nat(a0), z165),
    Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.double(Word.to_nat(32n, rw))),
    Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.double(Word.to_nat(32n, rw))), {==}), Equal.trans(Nat,
    Nat.add(bit_nat(a0), Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.double(Word.to_nat(32n, rw)))),
    Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw)))),
    Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.add(Nat.double(Word.to_nat(32n, rw)), bit_nat(a0))),
    M3.nat_add_lcomm(bit_nat(a0), Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.double(Word.to_nat(32n, rw))),
    Equal.cong(Nat, Nat, z166 => Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), z166), Nat.add(bit_nat(a0),
    Nat.double(Word.to_nat(32n, rw))), Nat.add(Nat.double(Word.to_nat(32n, rw)), bit_nat(a0)),
    M3.nat_add_comm(bit_nat(a0), Nat.double(Word.to_nat(32n, rw)))))))), Equal.cong(Nat, Nat,
        z167 => Nat.add(bit_nat(a0),
    z167), Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.double(Word.to_nat(32n, rw))),
    Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, qq), 10n), Word.to_nat(32n, rw))), Equal.sym(Nat,
    Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, qq), 10n), Word.to_nat(32n, rw))),
    Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.double(Word.to_nat(32n, rw))),
    M3.nat_double_add(Nat.mul(Word.to_nat(pp, qq), 10n), Word.to_nat(32n, rw))))))))

law dm_qr_b:
  for +uu: Unit
  for +pp: Nat
  for +a0: Bool
  for +qq: Word(pp)
  for rr: U32
  for hr: {Nat.is_lt(U32.to_nat(rr), 10n) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(dmr(1n+pp, U32.divmod.go.rec(pp, a0, 10, (qq, rr)))), 10n) == True{} : Bool}

def dm_qr_b(uu, pp, a0, qq, rr, hr):
  match rr:
    case U32{rw}:
      dm_rec_b(uu, pp, a0, qq, rw, hr)

law dm_qr_e:
  for +uu: Unit
  for +pp: Nat
  for +a0: Bool
  for +qq: Word(pp)
  for rr: U32
  for hr: {Nat.is_lt(U32.to_nat(rr), 10n) == True{} : Bool}
  {Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.rec(pp, a0, 10, (qq, rr)))), 10n), U32.to_nat(dmr(1n+pp,
    U32.divmod.go.rec(pp, a0, 10, (qq, rr))))) ==
    Nat.add(bit_nat(a0), Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, qq), 10n), U32.to_nat(rr)))) : Nat}

def dm_qr_e(uu, pp, a0, qq, rr, hr):
  match rr:
    case U32{rw}:
      dm_rec_e(uu, pp, a0, qq, rw, hr)

law dm_pr_b:
  for +uu: Unit
  for +pp: Nat
  for +a0: Bool
  for pr: Word(pp) & U32
  for hr: {Nat.is_lt(U32.to_nat(dmr(pp, pr)), 10n) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(dmr(1n+pp, U32.divmod.go.rec(pp, a0, 10, pr))), 10n) == True{} : Bool}

def dm_pr_b(uu, pp, a0, pr, hr):
  (qq, rr) = pr
  dm_qr_b(uu, pp, a0, qq, rr, hr)

law dm_pr_e:
  for +uu: Unit
  for +pp: Nat
  for +a0: Bool
  for pr: Word(pp) & U32
  for hr: {Nat.is_lt(U32.to_nat(dmr(pp, pr)), 10n) == True{} : Bool}
  {Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.rec(pp, a0, 10, pr))), 10n), U32.to_nat(dmr(1n+pp,
    U32.divmod.go.rec(pp, a0, 10, pr)))) ==
    Nat.add(bit_nat(a0), Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, dmq(pp, pr)), 10n), U32.to_nat(dmr(pp,
      pr))))) : Nat}

def dm_pr_e(uu, pp, a0, pr, hr):
  (qq, rr) = pr
  dm_qr_e(uu, pp, a0, qq, rr, hr)

# divmod.go by ten leaves a remainder below ten
law dm_b:
  for +uu: Unit
  for mm: Nat
  for aa: Word(mm)
  {Nat.is_lt(U32.to_nat(dmr(mm, U32.divmod.go(mm, aa, 10))), 10n) == True{} : Bool}

def dm_b(uu, mm, aa):
  match mm aa:
    case 0n WNil{}:
      {==}
    case 1n+(+pp) WCon{+a0, +hi}:
      dm_pr_b(uu, pp, a0, U32.divmod.go(pp, hi, 10), dm_b(uu, pp, hi))

# divmod.go by ten: ten times the quotient and the remainder are the word
law dm_e:
  for +uu: Unit
  for mm: Nat
  for aa: Word(mm)
  {Nat.add(Nat.mul(Word.to_nat(mm, dmq(mm, U32.divmod.go(mm, aa, 10))), 10n),
    U32.to_nat(dmr(mm, U32.divmod.go(mm, aa, 10)))) == Word.to_nat(mm, aa) : Nat}

def dm_e(uu, mm, aa):
  match mm aa:
    case 0n WNil{}:
      {==}
    case 1n+(+pp) WCon{+a0, +hi}:
      Equal.trans(Nat, Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.rec(pp, a0, 10, U32.divmod.go(pp,
        hi, 10)))), 10n), U32.to_nat(dmr(1n+pp, U32.divmod.go.rec(pp, a0, 10, U32.divmod.go(pp, hi, 10))))),
        Nat.add(bit_nat(a0), Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, dmq(pp, U32.divmod.go(pp, hi, 10))), 10n),
        U32.to_nat(dmr(pp, U32.divmod.go(pp, hi, 10)))))), Word.to_nat(1n+pp, WCon{a0, hi}), dm_pr_e(uu, pp, a0,
        U32.divmod.go(pp, hi, 10), dm_b(uu, pp, hi)), Equal.trans(Nat, Nat.add(bit_nat(a0),
        Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, dmq(pp, U32.divmod.go(pp, hi, 10))), 10n), U32.to_nat(dmr(pp,
        U32.divmod.go(pp, hi, 10)))))), Nat.add(bit_nat(a0), Nat.double(Word.to_nat(pp, hi))), Word.to_nat(1n+pp,
        WCon{a0, hi}), Equal.cong(Nat, Nat, z168 => Nat.add(bit_nat(a0), Nat.double(z168)),
        Nat.add(Nat.mul(Word.to_nat(pp, dmq(pp, U32.divmod.go(pp, hi, 10))), 10n), U32.to_nat(dmr(pp, U32.divmod.go(pp,
        hi, 10)))), Word.to_nat(pp, hi), dm_e(uu, pp, hi)), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{a0, hi}),
        Nat.add(bit_nat(a0), Nat.double(Word.to_nat(pp, hi))), w_nat_con(pp, a0, hi))))

# U32.div's result, from a division not yet known
law div_fin_eta:
  for pr: Word(32n) & U32
  {U32.div.fin(pr) == U32{dmq(32n, pr)} : U32}

def div_fin_eta(pr):
  (_qq, _rr) = pr
  {==}

# U32.mod's result, from a division not yet known
law mod_fin_eta:
  for pr: Word(32n) & U32
  {U32.mod.fin(pr) == dmr(32n, pr) : U32}

def mod_fin_eta(pr):
  (_qq, _rr) = pr
  {==}

# ten times a U32 over ten, and the remainder, are the U32
law u_div:
  for +uu: Unit
  for nn: U32
  {Nat.add(Nat.mul(U32.to_nat(U32.div(nn, 10)), 10n), U32.to_nat(U32.mod(nn, 10))) == U32.to_nat(nn) : Nat}

def u_div(uu, nn):
  match nn:
    case U32{+nw}:
      Equal.trans(Nat, Nat.add(Nat.mul(U32.to_nat(U32.div.fin(U32.divmod.go(32n, nw, 10))), 10n),
        U32.to_nat(U32.mod.fin(U32.divmod.go(32n, nw, 10)))), Nat.add(Nat.mul(U32.to_nat(U32{dmq(32n,
        U32.divmod.go(32n, nw, 10))}), 10n), U32.to_nat(U32.mod.fin(U32.divmod.go(32n, nw, 10)))), Word.to_nat(32n,
        nw), Equal.cong(U32, Nat, z169 => Nat.add(Nat.mul(U32.to_nat(z169), 10n),
        U32.to_nat(U32.mod.fin(U32.divmod.go(32n, nw, 10)))), U32.div.fin(U32.divmod.go(32n, nw, 10)), U32{dmq(32n,
        U32.divmod.go(32n, nw, 10))}, div_fin_eta(U32.divmod.go(32n, nw, 10))), Equal.trans(Nat,
        Nat.add(Nat.mul(U32.to_nat(U32{dmq(32n, U32.divmod.go(32n, nw, 10))}), 10n),
        U32.to_nat(U32.mod.fin(U32.divmod.go(32n, nw, 10)))), Nat.add(Nat.mul(U32.to_nat(U32{dmq(32n,
        U32.divmod.go(32n, nw, 10))}), 10n), U32.to_nat(dmr(32n, U32.divmod.go(32n, nw, 10)))), Word.to_nat(32n, nw),
        Equal.cong(U32, Nat, z170 => Nat.add(Nat.mul(U32.to_nat(U32{dmq(32n, U32.divmod.go(32n, nw, 10))}), 10n),
        U32.to_nat(z170)), U32.mod.fin(U32.divmod.go(32n, nw, 10)), dmr(32n, U32.divmod.go(32n, nw, 10)),
        mod_fin_eta(U32.divmod.go(32n, nw, 10))), dm_e(uu, 32n, nw)))

# a U32's remainder over ten is below ten
law u_mod:
  for +uu: Unit
  for nn: U32
  {Nat.is_lt(U32.to_nat(U32.mod(nn, 10)), 10n) == True{} : Bool}

def u_mod(uu, nn):
  match nn:
    case U32{+nw}:
      Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32.mod.fin(U32.divmod.go(32n, nw, 10))), 10n),
        Nat.is_lt(U32.to_nat(dmr(32n, U32.divmod.go(32n, nw, 10))), 10n), True{}, Equal.cong(U32, Bool,
        z171 => Nat.is_lt(U32.to_nat(z171), 10n), U32.mod.fin(U32.divmod.go(32n, nw, 10)), dmr(32n, U32.divmod.go(32n,
        nw, 10)), mod_fin_eta(U32.divmod.go(32n, nw, 10))), dm_b(uu, 32n, nw))

# laws/AsU32ReadsPlainDigits.bend: one step of U32.read

# ten times q and r below ten is ten times a and d below ten: q is a
law nat_div_uniq:
  for qq: Nat
  for aa: Nat
  for +rr: Nat
  for +dd: Nat
  for h: {Nat.add(Nat.mul(qq, 10n), rr) == Nat.add(Nat.mul(aa, 10n), dd) : Nat}
  for hr: {Nat.is_lt(rr, 10n) == True{} : Bool}
  for hd: {Nat.is_lt(dd, 10n) == True{} : Bool}
  {qq == aa : Nat}

def nat_div_uniq(qq, aa, rr, dd, h, hr, hd):
  match qq aa:
    case 0n 0n:
      {==}
    case 0n 1n+(+ap):
      Empty.absurd({0n == aa : Nat}, M1.true_false(Equal.trans(Bool, True{}, Nat.is_lt(rr, 10n), False{},
        Equal.sym(Bool, Nat.is_lt(rr, 10n), True{}, hr),
        Equal.trans(Bool, Nat.is_lt(rr, 10n), Nat.is_lt(Nat.add(Nat.add(10n, Nat.mul(ap, 10n)), dd), 10n), False{},
          Equal.cong(Nat, Bool, xx => Nat.is_lt(xx, 10n), rr, Nat.add(Nat.add(10n, Nat.mul(ap, 10n)), dd), h),
          nat_nlt_add(10n, Nat.add(Nat.mul(ap, 10n), dd))))))
    case 1n+(+qp) 0n:
      Empty.absurd({qq == 0n : Nat}, M1.true_false(Equal.trans(Bool, True{}, Nat.is_lt(dd, 10n), False{},
        Equal.sym(Bool, Nat.is_lt(dd, 10n), True{}, hd),
        Equal.trans(Bool, Nat.is_lt(dd, 10n), Nat.is_lt(Nat.add(Nat.add(10n, Nat.mul(qp, 10n)), rr), 10n), False{},
          Equal.cong(Nat, Bool, xx => Nat.is_lt(xx, 10n), dd, Nat.add(Nat.add(10n, Nat.mul(qp, 10n)), rr),
            Equal.sym(Nat, Nat.add(Nat.add(10n, Nat.mul(qp, 10n)), rr), dd, h)),
          nat_nlt_add(10n, Nat.add(Nat.mul(qp, 10n), rr))))))
    case 1n+(+qp) 1n+(+ap):
      Equal.cong(Nat, Nat, xx => 1n+xx, qp, ap, nat_div_uniq(qp, ap, rr, dd,
        M3.nat_add_cancel(10n, Nat.add(Nat.mul(qp, 10n), rr), Nat.add(Nat.mul(ap, 10n), dd), h), hr, hd))

# how many times 2^32 a step of U32.read passes
def step_ks(+aa: U32, dd: U32) -> Nat:
  Nat.add(uadd_k(U32.mul(aa, 10), dd), umk(aa))

# a step of U32.read as Nats: the new accumulator, and how many times it
# passes 2^32, is ten times the old one and the digit
law step_k:
  for +uu: Unit
  for +acc: U32
  for +dd: U32
  {Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)), Nat.mul(step_ks(acc, dd), M3.pow2u(32n,
    uu))) == Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(dd)) : Nat}

def step_k(uu, acc, dd):
  Equal.trans(Nat, Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)), Nat.mul(Nat.add(uadd_k(U32.mul(acc, 10), dd),
    umk(acc)), M3.pow2u(32n, uu))), Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)),
        Nat.add(Nat.mul(uadd_k(U32.mul(acc,
    10), dd), M3.pow2u(32n, uu)), Nat.mul(umk(acc), M3.pow2u(32n, uu)))), Nat.add(Nat.mul(U32.to_nat(acc), 10n),
    U32.to_nat(dd)), Equal.cong(Nat, Nat, z172 => Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)), z172),
    Nat.mul(Nat.add(uadd_k(U32.mul(acc, 10), dd), umk(acc)), M3.pow2u(32n, uu)), Nat.add(Nat.mul(uadd_k(U32.mul(acc,
        10),
    dd), M3.pow2u(32n, uu)), Nat.mul(umk(acc), M3.pow2u(32n, uu))), nat_mul_add_r(uadd_k(U32.mul(acc, 10), dd),
        umk(acc),
    M3.pow2u(32n, uu))), Equal.trans(Nat, Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)),
    Nat.add(Nat.mul(uadd_k(U32.mul(acc, 10), dd), M3.pow2u(32n, uu)), Nat.mul(umk(acc), M3.pow2u(32n, uu)))),
    Nat.add(Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)), Nat.mul(uadd_k(U32.mul(acc, 10), dd), M3.pow2u(32n,
        uu))),
    Nat.mul(umk(acc), M3.pow2u(32n, uu))), Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(dd)), Equal.sym(Nat,
    Nat.add(Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)), Nat.mul(uadd_k(U32.mul(acc, 10), dd), M3.pow2u(32n,
        uu))),
    Nat.mul(umk(acc), M3.pow2u(32n, uu))), Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)),
    Nat.add(Nat.mul(uadd_k(U32.mul(acc, 10), dd), M3.pow2u(32n, uu)), Nat.mul(umk(acc), M3.pow2u(32n, uu)))),
    M3.nat_add_assoc(U32.to_nat(U32.add(U32.mul(acc, 10), dd)), Nat.mul(uadd_k(U32.mul(acc, 10), dd), M3.pow2u(32n,
        uu)),
    Nat.mul(umk(acc), M3.pow2u(32n, uu)))), Equal.trans(Nat, Nat.add(Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)),
    Nat.mul(uadd_k(U32.mul(acc, 10), dd), M3.pow2u(32n, uu))), Nat.mul(umk(acc), M3.pow2u(32n, uu))),
    Nat.add(Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd)), Nat.mul(umk(acc), M3.pow2u(32n, uu))),
    Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(dd)), Equal.cong(Nat, Nat, z173 => Nat.add(z173,
    Nat.mul(umk(acc), M3.pow2u(32n, uu))), Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)),
        Nat.mul(uadd_k(U32.mul(acc,
    10), dd), M3.pow2u(32n, uu))), Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd)), u_add(uu, U32.mul(acc, 10),
    dd)), Equal.trans(Nat, Nat.add(Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd)), Nat.mul(umk(acc),
        M3.pow2u(32n,
    uu))), Nat.add(Nat.add(U32.to_nat(U32.mul(acc, 10)), Nat.mul(umk(acc), M3.pow2u(32n, uu))), U32.to_nat(dd)),
    Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(dd)), Equal.trans(Nat, Nat.add(Nat.add(U32.to_nat(U32.mul(acc,
    10)), U32.to_nat(dd)), Nat.mul(umk(acc), M3.pow2u(32n, uu))), Nat.add(Nat.mul(umk(acc), M3.pow2u(32n, uu)),
    Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd))), Nat.add(Nat.add(U32.to_nat(U32.mul(acc, 10)),
    Nat.mul(umk(acc), M3.pow2u(32n, uu))), U32.to_nat(dd)), Equal.trans(Nat, Nat.add(Nat.add(U32.to_nat(U32.mul(acc,
        10)),
    U32.to_nat(dd)), Nat.mul(umk(acc), M3.pow2u(32n, uu))), Nat.add(Nat.add(U32.to_nat(U32.mul(acc, 10)),
        U32.to_nat(dd)),
    Nat.mul(umk(acc), M3.pow2u(32n, uu))), Nat.add(Nat.mul(umk(acc), M3.pow2u(32n, uu)), Nat.add(U32.to_nat(U32.mul(acc,
    10)), U32.to_nat(dd))), Equal.cong(Nat, Nat, z174 => Nat.add(z174, Nat.mul(umk(acc), M3.pow2u(32n, uu))),
    Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd)), Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd)),
    {==}), Equal.trans(Nat, Nat.add(Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd)), Nat.mul(umk(acc),
        M3.pow2u(32n,
    uu))), Nat.add(U32.to_nat(U32.mul(acc, 10)), Nat.add(U32.to_nat(dd), Nat.mul(umk(acc), M3.pow2u(32n, uu)))),
    Nat.add(Nat.mul(umk(acc), M3.pow2u(32n, uu)), Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd))),
    M3.nat_add_assoc(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd), Nat.mul(umk(acc), M3.pow2u(32n, uu))),
        Equal.trans(Nat,
    Nat.add(U32.to_nat(U32.mul(acc, 10)), Nat.add(U32.to_nat(dd), Nat.mul(umk(acc), M3.pow2u(32n, uu)))),
    Nat.add(U32.to_nat(U32.mul(acc, 10)), Nat.add(Nat.mul(umk(acc), M3.pow2u(32n, uu)), U32.to_nat(dd))),
    Nat.add(Nat.mul(umk(acc), M3.pow2u(32n, uu)), Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd))),
        Equal.cong(Nat,
    Nat, z175 => Nat.add(U32.to_nat(U32.mul(acc, 10)), z175), Nat.add(U32.to_nat(dd), Nat.mul(umk(acc), M3.pow2u(32n,
    uu))), Nat.add(Nat.mul(umk(acc), M3.pow2u(32n, uu)), U32.to_nat(dd)), M3.nat_add_comm(U32.to_nat(dd),
        Nat.mul(umk(acc),
    M3.pow2u(32n, uu)))), M3.nat_add_lcomm(U32.to_nat(U32.mul(acc, 10)), Nat.mul(umk(acc), M3.pow2u(32n, uu)),
    U32.to_nat(dd))))), Equal.sym(Nat, Nat.add(Nat.add(U32.to_nat(U32.mul(acc, 10)), Nat.mul(umk(acc), M3.pow2u(32n,
    uu))), U32.to_nat(dd)), Nat.add(Nat.mul(umk(acc), M3.pow2u(32n, uu)), Nat.add(U32.to_nat(U32.mul(acc, 10)),
    U32.to_nat(dd))), Equal.trans(Nat, Nat.add(Nat.add(U32.to_nat(U32.mul(acc, 10)), Nat.mul(umk(acc), M3.pow2u(32n,
    uu))), U32.to_nat(dd)), Nat.add(Nat.add(Nat.mul(umk(acc), M3.pow2u(32n, uu)), U32.to_nat(U32.mul(acc, 10))),
    U32.to_nat(dd)), Nat.add(Nat.mul(umk(acc), M3.pow2u(32n, uu)), Nat.add(U32.to_nat(U32.mul(acc, 10)),
        U32.to_nat(dd))),
    Equal.cong(Nat, Nat, z176 => Nat.add(z176, U32.to_nat(dd)), Nat.add(U32.to_nat(U32.mul(acc, 10)), Nat.mul(umk(acc),
    M3.pow2u(32n, uu))), Nat.add(Nat.mul(umk(acc), M3.pow2u(32n, uu)), U32.to_nat(U32.mul(acc, 10))),
    M3.nat_add_comm(U32.to_nat(U32.mul(acc, 10)), Nat.mul(umk(acc), M3.pow2u(32n, uu)))),
        M3.nat_add_assoc(Nat.mul(umk(acc),
    M3.pow2u(32n, uu)), U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd))))), Equal.cong(Nat, Nat, z177 => Nat.add(z177,
    U32.to_nat(dd)), Nat.add(U32.to_nat(U32.mul(acc, 10)), Nat.mul(umk(acc), M3.pow2u(32n, uu))),
        Nat.mul(U32.to_nat(acc),
    10n), u_mul10(uu, acc))))))

# a step that stays below 2^32 is exact
law step_n:
  for +uu: Unit
  for +acc: U32
  for +dd: U32
  for h2: {Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(dd)), M3.pow2u(32n, uu)) == True{} : Bool}
  {U32.to_nat(U32.add(U32.mul(acc, 10), dd)) == Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(dd)) : Nat}

def step_n(uu, acc, dd, h2):
  nat_mod_small(step_ks(acc, dd), U32.to_nat(U32.add(U32.mul(acc, 10), dd)), Nat.add(Nat.mul(U32.to_nat(acc), 10n),
    U32.to_nat(dd)), M3.pow2u(32n, uu), step_k(uu, acc, dd), h2)

# a digit below ten that keeps the value below 2^32 passes U32.read's check
law step_ok:
  for +uu: Unit
  for +acc: U32
  for +dd: U32
  for h1: {Nat.is_lt(U32.to_nat(dd), 10n) == True{} : Bool}
  for h2: {Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(dd)), M3.pow2u(32n, uu)) == True{} : Bool}
  {U32.is_eq(U32.div(U32.add(U32.mul(acc, 10), dd), 10), acc) == True{} : Bool}

def step_ok(uu, acc, dd, h1, h2):
  Equal.trans(Bool, Cmp.is_eq(U32.cmp(U32.div(U32.add(U32.mul(acc, 10), dd), 10), acc)),
    Cmp.is_eq(Nat.cmp(U32.to_nat(U32.div(U32.add(U32.mul(acc, 10), dd), 10)), U32.to_nat(acc))), True{},
    Equal.cong(Cmp, Bool, z178 => Cmp.is_eq(z178), U32.cmp(U32.div(U32.add(U32.mul(acc, 10), dd), 10), acc),
    Nat.cmp(U32.to_nat(U32.div(U32.add(U32.mul(acc, 10), dd), 10)), U32.to_nat(acc)),
    u_cmp(U32.div(U32.add(U32.mul(acc, 10), dd), 10), acc)), Equal.trans(Bool,
    Cmp.is_eq(Nat.cmp(U32.to_nat(U32.div(U32.add(U32.mul(acc, 10), dd), 10)), U32.to_nat(acc))),
    Cmp.is_eq(Nat.cmp(U32.to_nat(acc), U32.to_nat(acc))), True{}, Equal.cong(Nat, Bool, z179 => Cmp.is_eq(Nat.cmp(z179,
    U32.to_nat(acc))), U32.to_nat(U32.div(U32.add(U32.mul(acc, 10), dd), 10)), U32.to_nat(acc),
    nat_div_uniq(U32.to_nat(U32.div(U32.add(U32.mul(acc, 10), dd), 10)), U32.to_nat(acc),
    U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10)), U32.to_nat(dd), Equal.trans(Nat,
    Nat.add(Nat.mul(U32.to_nat(U32.div(U32.add(U32.mul(acc, 10), dd), 10)), 10n),
    U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10))), U32.to_nat(U32.add(U32.mul(acc, 10), dd)),
    Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(dd)), u_div(uu, U32.add(U32.mul(acc, 10), dd)), step_n(uu, acc,
    dd, h2)), u_mod(uu, U32.add(U32.mul(acc, 10), dd)), h1)), Equal.cong(Cmp, Bool, z180 => Cmp.is_eq(z180),
    Nat.cmp(U32.to_nat(acc), U32.to_nat(acc)), EQ{}, nat_cmp_refl(U32.to_nat(acc)))))

# past U32.read's check, the remainder over ten is the digit
law step_rd:
  for +uu: Unit
  for +acc: U32
  for +dd: U32
  for h: {U32.is_eq(U32.div(U32.add(U32.mul(acc, 10), dd), 10), acc) == True{} : Bool}
  {U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10)) == U32.to_nat(dd) : Nat}

def step_rd(uu, acc, dd, h):
  nat_mod_small(step_ks(acc, dd), U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10)), U32.to_nat(dd), M3.pow2u(32n,
    uu), M3.nat_add_cancel(Nat.mul(U32.to_nat(acc), 10n), Nat.add(U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd),
        10)),
    Nat.mul(step_ks(acc, dd), M3.pow2u(32n, uu))), U32.to_nat(dd), Equal.trans(Nat, Nat.add(Nat.mul(U32.to_nat(acc),
        10n),
    Nat.add(U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10)), Nat.mul(step_ks(acc, dd), M3.pow2u(32n, uu)))),
    Nat.add(Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10))),
    Nat.mul(step_ks(acc, dd), M3.pow2u(32n, uu))), Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(dd)),
        Equal.sym(Nat,
    Nat.add(Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10))),
    Nat.mul(step_ks(acc, dd), M3.pow2u(32n, uu))), Nat.add(Nat.mul(U32.to_nat(acc), 10n),
    Nat.add(U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10)), Nat.mul(step_ks(acc, dd), M3.pow2u(32n, uu)))),
    M3.nat_add_assoc(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10)),
    Nat.mul(step_ks(acc, dd), M3.pow2u(32n, uu)))), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(U32.to_nat(acc), 10n),
    U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10))), Nat.mul(step_ks(acc, dd), M3.pow2u(32n, uu))),
    Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)), Nat.mul(step_ks(acc, dd), M3.pow2u(32n, uu))),
    Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(dd)), Equal.cong(Nat, Nat, z182 => Nat.add(z182,
    Nat.mul(step_ks(acc, dd), M3.pow2u(32n, uu))), Nat.add(Nat.mul(U32.to_nat(acc), 10n),
    U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10))), U32.to_nat(U32.add(U32.mul(acc, 10), dd)),
    Equal.trans(Nat, Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10))),
    Nat.add(Nat.mul(U32.to_nat(U32.div(U32.add(U32.mul(acc, 10), dd), 10)), 10n),
    U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10))), U32.to_nat(U32.add(U32.mul(acc, 10), dd)), Equal.cong(Nat,
    Nat, z181 => Nat.add(Nat.mul(z181, 10n), U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10))), U32.to_nat(acc),
    U32.to_nat(U32.div(U32.add(U32.mul(acc, 10), dd), 10)), Equal.sym(Nat, U32.to_nat(U32.div(U32.add(U32.mul(acc, 10),
    dd), 10)), U32.to_nat(acc), Equal.cong(U32, Nat, zz => U32.to_nat(zz), U32.div(U32.add(U32.mul(acc, 10), dd), 10),
    acc, M5.ueq(U32.div(U32.add(U32.mul(acc, 10), dd), 10), acc, h)))), u_div(uu, U32.add(U32.mul(acc, 10), dd)))),
    step_k(uu, acc, dd)))), M3.u_bound(uu, dd))

# past U32.read's check, the digit is below ten
law step_bad_d:
  for +uu: Unit
  for +acc: U32
  for +dd: U32
  for +h: {U32.is_eq(U32.div(U32.add(U32.mul(acc, 10), dd), 10), acc) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(dd), 10n) == True{} : Bool}

def step_bad_d(uu, acc, dd, h):
  Equal.trans(Bool, Nat.is_lt(U32.to_nat(dd), 10n), Nat.is_lt(U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10)),
    10n), True{}, Equal.cong(Nat, Bool, z183 => Nat.is_lt(z183, 10n), U32.to_nat(dd),
    U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10)), Equal.sym(Nat, U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10),
    dd), 10)), U32.to_nat(dd), step_rd(uu, acc, dd, h))), u_mod(uu, U32.add(U32.mul(acc, 10), dd)))

# past U32.read's check, the value stays below 2^32
law step_bad_t:
  for +uu: Unit
  for +acc: U32
  for +dd: U32
  for +h: {U32.is_eq(U32.div(U32.add(U32.mul(acc, 10), dd), 10), acc) == True{} : Bool}
  {Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(dd)), M3.pow2u(32n, uu)) == True{} : Bool}

def step_bad_t(uu, acc, dd, h):
  Equal.trans(Bool, Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(dd)), M3.pow2u(32n, uu)),
    Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10))),
    M3.pow2u(32n, uu)), True{}, Equal.cong(Nat, Bool, z184 => Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), z184),
    M3.pow2u(32n, uu)), U32.to_nat(dd), U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10)), Equal.sym(Nat,
    U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10)), U32.to_nat(dd), step_rd(uu, acc, dd, h))),
    Equal.trans(Bool, Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10),
    dd), 10))), M3.pow2u(32n, uu)), Nat.is_lt(U32.to_nat(U32.add(U32.mul(acc, 10), dd)), M3.pow2u(32n, uu)), True{},
    Equal.cong(Nat, Bool, z185 => Nat.is_lt(z185, M3.pow2u(32n, uu)), Nat.add(Nat.mul(U32.to_nat(acc), 10n),
    U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10))), U32.to_nat(U32.add(U32.mul(acc, 10), dd)),
    Equal.trans(Nat, Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10))),
    Nat.add(Nat.mul(U32.to_nat(U32.div(U32.add(U32.mul(acc, 10), dd), 10)), 10n),
    U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10))), U32.to_nat(U32.add(U32.mul(acc, 10), dd)), Equal.cong(Nat,
    Nat, z181 => Nat.add(Nat.mul(z181, 10n), U32.to_nat(U32.mod(U32.add(U32.mul(acc, 10), dd), 10))), U32.to_nat(acc),
    U32.to_nat(U32.div(U32.add(U32.mul(acc, 10), dd), 10)), Equal.sym(Nat, U32.to_nat(U32.div(U32.add(U32.mul(acc, 10),
    dd), 10)), U32.to_nat(acc), Equal.cong(U32, Nat, zz => U32.to_nat(zz), U32.div(U32.add(U32.mul(acc, 10), dd), 10),
    acc, M5.ueq(U32.div(U32.add(U32.mul(acc, 10), dd), 10), acc, h)))), u_div(uu, U32.add(U32.mul(acc, 10), dd)))),
    M3.u_bound(uu, U32.add(U32.mul(acc, 10), dd))))

# a Cmp below EQ is not at least EQ
law cmp_lt_nge:
  for cc: Cmp
  for h: {Cmp.is_lt(cc) == True{} : Bool}
  {Cmp.is_ge(cc) == False{} : Bool}

def cmp_lt_nge(cc, h):
  match cc:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({True{} == False{} : Bool}, M2.false_true(h))
    case GT{}:
      Empty.absurd({True{} == False{} : Bool}, M2.false_true(h))

# a Cmp not below EQ is at least EQ
law cmp_nlt_ge:
  for cc: Cmp
  for h: {Cmp.is_lt(cc) == False{} : Bool}
  {Cmp.is_ge(cc) == True{} : Bool}

def cmp_nlt_ge(cc, h):
  match cc:
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, M1.true_false(h))
    case EQ{}:
      {==}
    case GT{}:
      {==}

# below b + 1 is at most b
law nat_lt_le:
  for aa: Nat
  for bb: Nat
  {Nat.is_lt(aa, 1n+bb) == Cmp.is_le(Nat.cmp(aa, bb)) : Bool}

def nat_lt_le(aa, bb):
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+_bp:
      {==}
    case 1n+ap 0n:
      nat_nlt_zero(ap)
    case 1n+ap 1n+bp:
      nat_lt_le(ap, bp)

# a Bool that is not True is False
law bool_false:
  for bb: Bool
  for h: {bb == True{} : Bool} -> Empty
  {bb == False{} : Bool}

def bool_false(bb, h):
  match bb:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, h({==}))

# the code point less 48 is below ten exactly for a digit, once whether it
# is below 48 is known
law dig_nat:
  for +uu: Unit
  for +xx: U32
  for lt: Bool
  for +elt: {Nat.is_lt(U32.to_nat(xx), 48n) == lt : Bool}
  {Nat.is_lt(U32.to_nat(U32.sub(xx, 48)), 10n) == Bool.and(Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 48n)),
    Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n))) : Bool}

def dig_nat(uu, xx, lt, elt):
  match lt:
    case True{}:
      Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32.sub(xx, 48)), 10n), False{},
        Bool.and(Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 48n)), Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n))),
        bool_false(Nat.is_lt(U32.to_nat(U32.sub(xx, 48)), 10n), hh => M1.true_false(Equal.trans(Bool, True{},
          Nat.is_lt(U32.to_nat(U32.sub(xx, 48)), 10n), Nat.is_lt(Nat.add(Nat.add(64n, pz6(26n, uu)), U32.to_nat(xx)),
          58n), Equal.sym(Bool, Nat.is_lt(U32.to_nat(U32.sub(xx, 48)), 10n), True{}, hh), Equal.trans(Bool,
          Nat.is_lt(U32.to_nat(U32.sub(xx, 48)), 10n), Nat.is_lt(Nat.add(U32.to_nat(U32.sub(xx, 48)), 48n), 58n),
          Nat.is_lt(Nat.add(Nat.add(64n, pz6(26n, uu)), U32.to_nat(xx)), 58n), Equal.cong(Nat, Bool,
          z186 => Nat.is_lt(z186, 58n), Nat.add(48n, U32.to_nat(U32.sub(xx, 48))), Nat.add(U32.to_nat(U32.sub(xx, 48)),
          48n), M3.nat_add_comm(48n, U32.to_nat(U32.sub(xx, 48)))), Equal.trans(Bool,
          Nat.is_lt(Nat.add(U32.to_nat(U32.sub(xx, 48)), 48n), 58n), Nat.is_lt(Nat.add(U32.to_nat(xx), M3.pow2u(32n,
              uu)),
          58n), Nat.is_lt(Nat.add(Nat.add(64n, pz6(26n, uu)), U32.to_nat(xx)), 58n), Equal.cong(Nat, Bool,
          z187 => Nat.is_lt(z187, 58n), Nat.add(U32.to_nat(U32.sub(xx, 48)), 48n), Nat.add(U32.to_nat(xx), M3.pow2u(32n,
          uu)), u_sub_lt(uu, xx, 48, elt)), Equal.trans(Bool, Nat.is_lt(Nat.add(U32.to_nat(xx), M3.pow2u(32n, uu)),
              58n),
          Nat.is_lt(Nat.add(M3.pow2u(32n, uu), U32.to_nat(xx)), 58n), Nat.is_lt(Nat.add(Nat.add(64n, pz6(26n, uu)),
          U32.to_nat(xx)), 58n), Equal.cong(Nat, Bool, z188 => Nat.is_lt(z188, 58n), Nat.add(U32.to_nat(xx),
              M3.pow2u(32n,
          uu)), Nat.add(M3.pow2u(32n, uu), U32.to_nat(xx)), M3.nat_add_comm(U32.to_nat(xx), M3.pow2u(32n, uu))),
              Equal.cong(Nat,
          Bool, z189 => Nat.is_lt(Nat.add(z189, U32.to_nat(xx)), 58n), M3.pow2u(32n, uu), Nat.add(64n, pz6(26n, uu)),
          pw_big(26n, uu)))))))),
        Equal.cong(Bool, Bool, zz => Bool.and(zz, Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n))), False{},
          Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 48n)),
          Equal.sym(Bool, Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 48n)), False{}, cmp_lt_nge(Nat.cmp(U32.to_nat(xx), 48n),
            elt))))
    case False{}:
      Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32.sub(xx, 48)), 10n), Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n)),
        Bool.and(Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 48n)), Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n))), Equal.trans(Bool,
        Nat.is_lt(U32.to_nat(U32.sub(xx, 48)), 10n), Nat.is_lt(Nat.add(U32.to_nat(U32.sub(xx, 48)), 48n), 58n),
        Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n)), Equal.cong(Nat, Bool, z190 => Nat.is_lt(z190, 58n), Nat.add(48n,
        U32.to_nat(U32.sub(xx, 48))), Nat.add(U32.to_nat(U32.sub(xx, 48)), 48n), M3.nat_add_comm(48n,
        U32.to_nat(U32.sub(xx, 48)))), Equal.trans(Bool, Nat.is_lt(Nat.add(U32.to_nat(U32.sub(xx, 48)), 48n), 58n),
        Nat.is_lt(U32.to_nat(xx), 58n), Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n)), Equal.cong(Nat, Bool,
        z191 => Nat.is_lt(z191, 58n), Nat.add(U32.to_nat(U32.sub(xx, 48)), 48n), U32.to_nat(xx), u_sub_ge(uu, xx, 48,
        elt)), nat_lt_le(U32.to_nat(xx), 57n))),
        Equal.cong(Bool, Bool, zz => Bool.and(zz, Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n))), True{},
          Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 48n)),
          Equal.sym(Bool, Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 48n)), True{}, cmp_nlt_ge(Nat.cmp(U32.to_nat(xx), 48n),
            elt))))

# the code point less 48 is below ten exactly for a digit
law dig_lt:
  for +uu: Unit
  for +xx: U32
  {Nat.is_lt(U32.to_nat(U32.sub(xx, 48)), 10n) == D2.digit(Chr{xx}) : Bool}

def dig_lt(uu, xx):
  Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32.sub(xx, 48)), 10n), Bool.and(Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 48n)),
    Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n))), Bool.and(Cmp.is_ge(U32.cmp(xx, 48)), Cmp.is_le(U32.cmp(xx, 57))),
    dig_nat(uu, xx, Nat.is_lt(U32.to_nat(xx), 48n), {==}),
    Equal.trans(Bool, Bool.and(Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 48n)), Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n))),
      Bool.and(Cmp.is_ge(U32.cmp(xx, 48)), Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n))), Bool.and(Cmp.is_ge(U32.cmp(xx,
      48)), Cmp.is_le(U32.cmp(xx, 57))),
    Equal.cong(Cmp, Bool, zz => Bool.and(Cmp.is_ge(zz), Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n))),
      Nat.cmp(U32.to_nat(xx), 48n), U32.cmp(xx, 48),
      Equal.sym(Cmp, U32.cmp(xx, 48), Nat.cmp(U32.to_nat(xx), 48n), u_cmp(xx, 48))),
    Equal.cong(Cmp, Bool, zz => Bool.and(Cmp.is_ge(U32.cmp(xx, 48)), Cmp.is_le(zz)), Nat.cmp(U32.to_nat(xx), 57n),
      U32.cmp(xx, 57),
      Equal.sym(Cmp, U32.cmp(xx, 57), Nat.cmp(U32.to_nat(xx), 57n), u_cmp(xx, 57)))))

# a digit's value, once whether it is below 48 is known
law dig_val_nat:
  for +uu: Unit
  for +xx: U32
  for lt: Bool
  for +elt: {Nat.is_lt(U32.to_nat(xx), 48n) == lt : Bool}
  for h: {Bool.and(Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 48n)), Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n))) == True{} : Bool}
  {U32.to_nat(U32.sub(xx, 48)) == Nat.sub(U32.to_nat(xx), 48n) : Nat}

def dig_val_nat(uu, xx, lt, elt, h):
  match lt:
    case True{}:
      Empty.absurd({U32.to_nat(U32.sub(xx, 48)) == Nat.sub(U32.to_nat(xx), 48n) : Nat}, M2.false_true(Equal.trans(Bool,
        False{}, Bool.and(Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 48n)), Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n))), True{},
        Equal.cong(Bool, Bool, zz => Bool.and(zz, Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n))), False{},
          Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 48n)),
          Equal.sym(Bool, Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 48n)), False{}, cmp_lt_nge(Nat.cmp(U32.to_nat(xx), 48n),
            elt))), h)))
    case False{}:
      Equal.sym(Nat, Nat.sub(U32.to_nat(xx), 48n), U32.to_nat(U32.sub(xx, 48)),
        Equal.trans(Nat, Nat.sub(U32.to_nat(xx), 48n), Nat.sub(Nat.add(U32.to_nat(U32.sub(xx, 48)), 48n), 48n),
          U32.to_nat(U32.sub(xx, 48)),
          Equal.cong(Nat, Nat, zz => Nat.sub(zz, 48n), U32.to_nat(xx), Nat.add(U32.to_nat(U32.sub(xx, 48)), 48n),
            Equal.sym(Nat, Nat.add(U32.to_nat(U32.sub(xx, 48)), 48n), U32.to_nat(xx), u_sub_ge(uu, xx, 48, elt))),
          Equal.trans(Nat, Nat.sub(Nat.add(U32.to_nat(U32.sub(xx, 48)), 48n), 48n), Nat.sub(Nat.add(48n,
            U32.to_nat(U32.sub(xx, 48))), 48n), U32.to_nat(U32.sub(xx, 48)),
            Equal.cong(Nat, Nat, zz => Nat.sub(zz, 48n), Nat.add(U32.to_nat(U32.sub(xx, 48)), 48n), Nat.add(48n,
              U32.to_nat(U32.sub(xx, 48))), M3.nat_add_comm(U32.to_nat(U32.sub(xx, 48)), 48n)),
            M3.nat_sub_zero(U32.to_nat(U32.sub(xx, 48))))))

# a digit's value is its code point less 48
law dig_val:
  for +uu: Unit
  for +xx: U32
  for h: {D2.digit(Chr{xx}) == True{} : Bool}
  {U32.to_nat(U32.sub(xx, 48)) == Nat.sub(U32.to_nat(xx), 48n) : Nat}

def dig_val(uu, xx, h):
  dig_val_nat(uu, xx, Nat.is_lt(U32.to_nat(xx), 48n), {==}, Equal.trans(Bool,
    Bool.and(Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 48n)), Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n))),
    Bool.and(Cmp.is_ge(U32.cmp(xx, 48)), Cmp.is_le(U32.cmp(xx, 57))), True{},
    Equal.trans(Bool, Bool.and(Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 48n)), Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n))),
      Bool.and(Cmp.is_ge(U32.cmp(xx, 48)), Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n))), Bool.and(Cmp.is_ge(U32.cmp(xx,
      48)), Cmp.is_le(U32.cmp(xx, 57))),
    Equal.cong(Cmp, Bool, zz => Bool.and(Cmp.is_ge(zz), Cmp.is_le(Nat.cmp(U32.to_nat(xx), 57n))),
      Nat.cmp(U32.to_nat(xx), 48n), U32.cmp(xx, 48),
      Equal.sym(Cmp, U32.cmp(xx, 48), Nat.cmp(U32.to_nat(xx), 48n), u_cmp(xx, 48))),
    Equal.cong(Cmp, Bool, zz => Bool.and(Cmp.is_ge(U32.cmp(xx, 48)), Cmp.is_le(zz)), Nat.cmp(U32.to_nat(xx), 57n),
      U32.cmp(xx, 57),
      Equal.sym(Cmp, U32.cmp(xx, 57), Nat.cmp(U32.to_nat(xx), 57n), u_cmp(xx, 57)))), h))

# laws/AsU32ReadsPlainDigits.bend: fits, and the spec's texts

# half of v is below y exactly when v is below twice y
law half_lt:
  for vv: Nat
  for yy: Nat
  {Nat.is_lt(D1.half(vv), yy) == Nat.is_lt(vv, Nat.double(yy)) : Bool}

def half_lt(vv, yy):
  match vv:
    case 0n:
      match yy:
        case 0n:
          {==}
        case 1n+_yp:
          {==}
    case 1n+pv:
      match pv:
        case 0n:
          match yy:
            case 0n:
              {==}
            case 1n+_yp:
              {==}
        case 1n+qq:
          match yy:
            case 0n:
              {==}
            case 1n+yp:
              half_lt(qq, yp)

# fitting in kk bits is being below 2^kk
law fits_lt:
  for +kk: Nat
  for +vv: Nat
  {Laws.fits(kk, vv) == Nat.is_lt(vv, M3.pow2(kk)) : Bool}

def fits_lt(kk, vv):
  match kk:
    case 0n:
      match vv:
        case 0n:
          {==}
        case 1n+vp:
          Equal.sym(Bool, Nat.is_lt(vp, 0n), False{}, nat_nlt_zero(vp))
    case 1n+(+pp):
      Equal.trans(Bool, Laws.fits(pp, D1.half(vv)), Nat.is_lt(D1.half(vv), M3.pow2(pp)), Nat.is_lt(vv,
        Nat.double(M3.pow2(pp))),
        fits_lt(pp, D1.half(vv)), half_lt(vv, M3.pow2(pp)))

# fits_lt, with 2^kk named through uu
law fits_lt_u:
  for +kk: Nat
  for uu: Unit
  for +vv: Nat
  {Laws.fits(kk, vv) == Nat.is_lt(vv, M3.pow2u(kk, uu)) : Bool}

def fits_lt_u(kk, uu, vv):
  match uu:
    case Unit{}:
      fits_lt(kk, vv)

# a true when: its condition
law when_c:
  for cc: Bool
  for -yy: Bool
  for h: {D1.when(cc, yy, False{}) == True{} : Bool}
  {cc == True{} : Bool}

def when_c(cc, _yy, h):
  match cc:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, M2.false_true(h))

# a true when: its first branch
law when_y:
  for cc: Bool
  for -yy: Bool
  for h: {D1.when(cc, yy, False{}) == True{} : Bool}
  {yy == True{} : Bool}

def when_y(cc, _yy, h):
  match cc:
    case True{}:
      h
    case False{}:
      Empty.absurd({_yy == True{} : Bool}, M2.false_true(h))

# ten times v is v and nine times v
law nat_mul10:
  for +vv: Nat
  {Nat.mul(vv, 10n) == Nat.add(vv, Nat.mul(vv, 9n)) : Nat}

def nat_mul10(vv):
  Equal.trans(Nat, Nat.mul(vv, 10n), Nat.add(Nat.mul(vv, 1n), Nat.mul(vv, 9n)), Nat.add(vv, Nat.mul(vv, 9n)),
    nat_mul_add_l(vv, 1n, 9n),
    Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.mul(vv, 9n)), Nat.mul(vv, 1n), vv, nat_mul_one(vv)))

# reading more digits never lowers the value below a bound it has reached
law dec_val_ge:
  for +cs: List<&2, Char>
  for +vv: Nat
  for +tt: Nat
  for h: {Nat.is_lt(vv, tt) == False{} : Bool}
  {Nat.is_lt(Laws.dec_val(cs, vv), tt) == False{} : Bool}

def dec_val_ge(cs, vv, tt, h):
  match cs:
    case Nil{}:
      h
    case ch <> tl:
      dec_val_ge(tl, Nat.add(Nat.mul(vv, 10n), Nat.sub(U32.to_nat(Char.to_u32(ch)), 48n)), tt,
        Equal.trans(Bool, Nat.is_lt(Nat.add(Nat.mul(vv, 10n), Nat.sub(U32.to_nat(Char.to_u32(ch)), 48n)), tt),
          Nat.is_lt(Nat.add(vv, Nat.add(Nat.mul(vv, 9n), Nat.sub(U32.to_nat(Char.to_u32(ch)), 48n))), tt), False{},
          Equal.cong(Nat, Bool, zz => Nat.is_lt(zz, tt), Nat.add(Nat.mul(vv, 10n), Nat.sub(U32.to_nat(Char.to_u32(ch)),
            48n)),
            Nat.add(vv, Nat.add(Nat.mul(vv, 9n), Nat.sub(U32.to_nat(Char.to_u32(ch)), 48n))),
            Equal.trans(Nat, Nat.add(Nat.mul(vv, 10n), Nat.sub(U32.to_nat(Char.to_u32(ch)), 48n)),
              Nat.add(Nat.add(vv, Nat.mul(vv, 9n)), Nat.sub(U32.to_nat(Char.to_u32(ch)), 48n)),
              Nat.add(vv, Nat.add(Nat.mul(vv, 9n), Nat.sub(U32.to_nat(Char.to_u32(ch)), 48n))),
              Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.sub(U32.to_nat(Char.to_u32(ch)), 48n)), Nat.mul(vv, 10n),
                Nat.add(vv, Nat.mul(vv, 9n)), nat_mul10(vv)),
              M3.nat_add_assoc(vv, Nat.mul(vv, 9n), Nat.sub(U32.to_nat(Char.to_u32(ch)), 48n)))),
          nat_ge_add(vv, Nat.add(Nat.mul(vv, 9n), Nat.sub(U32.to_nat(Char.to_u32(ch)), 48n)), tt, h)))

# laws/AsU32ReadsPlainDigits.bend: U32.read over digits

# one step of U32.read over a digit, once whether the value stays below 2^32
# is known
law rd_step:
  for +uu: Unit
  for +acc: U32
  for +xx: U32
  for +tt: String
  for bb: Bool
  for +eb: {Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(U32.sub(xx, 48))), M3.pow2u(32n,
      uu)) == bb : Bool}
  for h1: {Nat.is_lt(U32.to_nat(U32.sub(xx, 48)), 10n) == True{} : Bool}
  for ih: {Laws.u32_nat(U32.read.go(tt, U32.add(U32.mul(acc, 10), U32.sub(xx, 48)))) == Laws.nat_if(Laws.fits(32n,
    Laws.dec_val(String.to_list(tt), U32.to_nat(U32.add(U32.mul(acc, 10), U32.sub(xx, 48))))),
    Laws.dec_val(String.to_list(tt), U32.to_nat(U32.add(U32.mul(acc, 10), U32.sub(xx, 48))))) : Maybe<&2, Nat>}
  {Laws.u32_nat(U32.read.if(tt, U32.add(U32.mul(acc, 10), U32.sub(xx, 48)), U32.is_eq(U32.div(U32.add(U32.mul(acc, 10),
    U32.sub(xx, 48)), 10), acc))) == Laws.nat_if(Laws.fits(32n, Laws.dec_val(String.to_list(tt),
    Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(U32.sub(xx, 48))))), Laws.dec_val(String.to_list(tt),
    Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(U32.sub(xx, 48))))) : Maybe<&2, Nat>}

def rd_step(uu, acc, xx, tt, bb, eb, h1, ih):
  match bb:
    case True{}:
      ok = Equal.sym(Bool, U32.is_eq(U32.div(U32.add(U32.mul(acc, 10), U32.sub(xx, 48)), 10), acc), True{}, step_ok(uu,
        acc, U32.sub(xx, 48), h1, eb))
      %ok : {Laws.u32_nat(U32.read.if(tt, U32.add(U32.mul(acc, 10), U32.sub(xx, 48)), _)) == Laws.nat_if(Laws.fits(32n,
        Laws.dec_val(String.to_list(tt), Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(U32.sub(xx, 48))))),
        Laws.dec_val(String.to_list(tt), Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(U32.sub(xx,
        48))))) : Maybe<&2, Nat>}
      Equal.trans(Maybe<&2, Nat>, Laws.u32_nat(U32.read.go(tt, U32.add(U32.mul(acc, 10), U32.sub(xx, 48)))),
        Laws.nat_if(Laws.fits(32n, Laws.dec_val(String.to_list(tt), U32.to_nat(U32.add(U32.mul(acc, 10), U32.sub(xx,
        48))))), Laws.dec_val(String.to_list(tt), U32.to_nat(U32.add(U32.mul(acc, 10), U32.sub(xx, 48))))),
        Laws.nat_if(Laws.fits(32n, Laws.dec_val(String.to_list(tt), Nat.add(Nat.mul(U32.to_nat(acc), 10n),
        U32.to_nat(U32.sub(xx, 48))))), Laws.dec_val(String.to_list(tt), Nat.add(Nat.mul(U32.to_nat(acc), 10n),
        U32.to_nat(U32.sub(xx, 48))))), ih,
        Equal.cong(Nat, Maybe<&2, Nat>, zz => Laws.nat_if(Laws.fits(32n, Laws.dec_val(String.to_list(tt), zz)),
          Laws.dec_val(String.to_list(tt), zz)), U32.to_nat(U32.add(U32.mul(acc, 10), U32.sub(xx, 48))),
          Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(U32.sub(xx, 48))), step_n(uu, acc, U32.sub(xx, 48), eb)))
    case False{}:
      bad = Equal.sym(Bool, U32.is_eq(U32.div(U32.add(U32.mul(acc, 10), U32.sub(xx, 48)), 10), acc), False{},
        bool_false(U32.is_eq(U32.div(U32.add(U32.mul(acc, 10), U32.sub(xx, 48)), 10), acc),
        hh => M1.true_false(Equal.trans(Bool, True{},
        Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(U32.sub(xx, 48))), M3.pow2u(32n, uu)), False{},
        Equal.sym(Bool, Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(U32.sub(xx, 48))), M3.pow2u(32n,
            uu)),
          True{}, step_bad_t(uu, acc, U32.sub(xx, 48), hh)), eb))))
      %bad : {Laws.u32_nat(U32.read.if(tt, U32.add(U32.mul(acc, 10), U32.sub(xx, 48)),
        _)) == Laws.nat_if(Laws.fits(32n, Laws.dec_val(String.to_list(tt), Nat.add(Nat.mul(U32.to_nat(acc), 10n),
        U32.to_nat(U32.sub(xx, 48))))), Laws.dec_val(String.to_list(tt), Nat.add(Nat.mul(U32.to_nat(acc), 10n),
        U32.to_nat(U32.sub(xx, 48))))) : Maybe<&2, Nat>}
      big = Equal.sym(Bool, Laws.fits(32n, Laws.dec_val(String.to_list(tt), Nat.add(Nat.mul(U32.to_nat(acc), 10n),
        U32.to_nat(U32.sub(xx, 48))))), False{},
        Equal.trans(Bool, Laws.fits(32n, Laws.dec_val(String.to_list(tt), Nat.add(Nat.mul(U32.to_nat(acc), 10n),
          U32.to_nat(U32.sub(xx, 48))))), Nat.is_lt(Laws.dec_val(String.to_list(tt), Nat.add(Nat.mul(U32.to_nat(acc),
          10n), U32.to_nat(U32.sub(xx, 48)))), M3.pow2u(32n, uu)), False{},
          fits_lt_u(32n, uu, Laws.dec_val(String.to_list(tt), Nat.add(Nat.mul(U32.to_nat(acc), 10n),
            U32.to_nat(U32.sub(xx, 48))))), dec_val_ge(String.to_list(tt), Nat.add(Nat.mul(U32.to_nat(acc), 10n),
            U32.to_nat(U32.sub(xx, 48))), M3.pow2u(32n, uu), eb)))
      %big : {None{} == Laws.nat_if(_, Laws.dec_val(String.to_list(tt), Nat.add(Nat.mul(U32.to_nat(acc), 10n),
        U32.to_nat(U32.sub(xx, 48))))) : Maybe<&2, Nat>}
      {==}

# over digits, U32.read reads their value when it is below 2^32, else none
law read_all:
  for +uu: Unit
  for ss: String
  for +acc: U32
  for +h: {D1.digits_end(String.to_list(ss)) == True{} : Bool}
  {Laws.u32_nat(U32.read.go(ss, acc)) == Laws.nat_if(Laws.fits(32n, Laws.dec_val(String.to_list(ss), U32.to_nat(acc))),
    Laws.dec_val(String.to_list(ss), U32.to_nat(acc))) : Maybe<&2, Nat>}

def read_all(uu, ss, acc, h):
  match ss:
    case SNil{}:
      ee = Equal.sym(Bool, Laws.fits(32n, U32.to_nat(acc)), True{},
        Equal.trans(Bool, Laws.fits(32n, U32.to_nat(acc)), Nat.is_lt(U32.to_nat(acc), M3.pow2u(32n, uu)), True{},
          fits_lt_u(32n, uu, U32.to_nat(acc)), M3.u_bound(uu, acc)))
      %ee : {Some{U32.to_nat(acc)} == Laws.nat_if(_, U32.to_nat(acc)) : Maybe<&2, Nat>}
      {==}
    case SCon{Chr{+xx}, +tt}:
      +hd = when_c(D2.digit(Chr{xx}), D1.digits_end(String.to_list(tt)), h)
      dv = dig_val(uu, xx, hd)
      %dv : {Laws.u32_nat(U32.read.if(tt, U32.add(U32.mul(acc, 10), U32.sub(xx, 48)),
        U32.is_eq(U32.div(U32.add(U32.mul(acc, 10), U32.sub(xx, 48)), 10), acc))) ==
        Laws.nat_if(Laws.fits(32n, Laws.dec_val(String.to_list(tt), Nat.add(Nat.mul(U32.to_nat(acc), 10n), _))),
          Laws.dec_val(String.to_list(tt), Nat.add(Nat.mul(U32.to_nat(acc), 10n), _))) : Maybe<&2, Nat>}
      rd_step(uu, acc, xx, tt, Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(U32.sub(xx, 48))),
        M3.pow2u(32n, uu)), {==},
        Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32.sub(xx, 48)), 10n), D2.digit(Chr{xx}), True{}, dig_lt(uu, xx), hd),
        read_all(uu, tt, U32.add(U32.mul(acc, 10), U32.sub(xx, 48)), when_y(D2.digit(Chr{xx}),
          D1.digits_end(String.to_list(tt)), h)))

# U32.read.if on a false check is none, and on a true one continues
law rif_f:
  for tt: String
  for nn: U32
  for bb: Bool
  for h: {bb == False{} : Bool}
  {U32.read.if(tt, nn, bb) == None{} : Maybe<&2, U32>}

def rif_f(_tt, _nn, bb, h):
  match bb:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({U32.read.if(_tt, _nn, True{}) == None{} : Maybe<&2, U32>}, M1.true_false(h))

# U32.read.if whose continuation is none is none
law rif_n:
  for tt: String
  for +nn: U32
  for bb: Bool
  for h: {U32.read.go(tt, nn) == None{} : Maybe<&2, U32>}
  {U32.read.if(tt, nn, bb) == None{} : Maybe<&2, U32>}

def rif_n(_tt, _nn, bb, h):
  match bb:
    case False{}:
      {==}
    case True{}:
      h

# one step of U32.read, once whether the character is a digit is known,
# when some character is not a digit
law rb_step:
  for +uu: Unit
  for +acc: U32
  for +xx: U32
  for +tt: String
  for dg: Bool
  for edg: {D2.digit(Chr{xx}) == dg : Bool}
  for h: {D1.when(dg, D1.digits_end(String.to_list(tt)), False{}) == False{} : Bool}
  for ih: {D1.digits_end(String.to_list(tt)) == False{} : Bool} -> {U32.read.go(tt, U32.add(U32.mul(acc, 10),
    U32.sub(xx, 48))) == None{} : Maybe<&2, U32>}
  {U32.read.if(tt, U32.add(U32.mul(acc, 10), U32.sub(xx, 48)), U32.is_eq(U32.div(U32.add(U32.mul(acc, 10), U32.sub(xx,
    48)), 10), acc)) == None{} : Maybe<&2, U32>}

def rb_step(uu, acc, xx, tt, dg, edg, h, ih):
  match dg:
    case True{}:
      rif_n(tt, U32.add(U32.mul(acc, 10), U32.sub(xx, 48)), U32.is_eq(U32.div(U32.add(U32.mul(acc, 10), U32.sub(xx,
        48)), 10), acc), ih(h))
    case False{}:
      rif_f(tt, U32.add(U32.mul(acc, 10), U32.sub(xx, 48)), U32.is_eq(U32.div(U32.add(U32.mul(acc, 10), U32.sub(xx,
        48)), 10), acc), bool_false(U32.is_eq(U32.div(U32.add(U32.mul(acc, 10), U32.sub(xx, 48)), 10), acc),
        hh => M1.true_false(Equal.trans(Bool, True{}, Nat.is_lt(U32.to_nat(U32.sub(xx, 48)), 10n), False{},
        Equal.sym(Bool, Nat.is_lt(U32.to_nat(U32.sub(xx, 48)), 10n), True{}, step_bad_d(uu, acc, U32.sub(xx, 48), hh)),
        Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32.sub(xx, 48)), 10n), D2.digit(Chr{xx}), False{}, dig_lt(uu, xx),
          edg)))))

# over a text with a character that is not a digit, U32.read is none
law read_bad:
  for +uu: Unit
  for ss: String
  for +acc: U32
  for h: {D1.digits_end(String.to_list(ss)) == False{} : Bool}
  {U32.read.go(ss, acc) == None{} : Maybe<&2, U32>}

def read_bad(uu, ss, acc, h):
  match ss:
    case SNil{}:
      Empty.absurd({Some{acc} == None{} : Maybe<&2, U32>}, M1.true_false(h))
    case SCon{Chr{+xx}, +tt}:
      rb_step(uu, acc, xx, tt, D2.digit(Chr{xx}), {==}, h, hh => read_bad(uu, tt, U32.add(U32.mul(acc, 10),
        U32.sub(xx, 48)), hh))

# laws/AsU32ReadsPlainDigits.bend: the decimals are the JSON numbers that are all digits

# a character that is some code point is a character of it
law cp_eq:
  for xx: U32
  for kk: U32
  for +h: {D1.is_cp(Chr{xx}, kk) == True{} : Bool}
  {kk == xx : U32}

def cp_eq(xx, kk, h):
  Equal.sym(U32, xx, kk, M5.ueq(xx, kk, h))

# digits_end then digits_rest: digits end the rest of an int
law de_dr:
  for +cs: List<&2, Char>
  for +h: {D1.digits_end(cs) == True{} : Bool}
  {D1.digits_rest(cs) == True{} : Bool}

def de_dr(cs, h):
  match cs:
    case Nil{}:
      {==}
    case +ch <> +tl:
      dg = Equal.sym(Bool, D2.digit(ch), True{}, when_c(D2.digit(ch), D1.digits_end(tl), h))
      %dg : {D1.when(_, D1.digits_rest(tl), D1.when(D1.is_cp(ch, 46), D1.frac_body(tl),
        D1.when(D1.is_e(ch), D1.exp_body(tl), False{}))) == True{} : Bool}
      de_dr(tl, when_y(D2.digit(ch), D1.digits_end(tl), h))

# nothing left: zero_rest holds
law nm_zr:
  for cs: List<&2, Char>
  for +h: {D1.no_more(cs) == True{} : Bool}
  {D1.zero_rest(cs) == True{} : Bool}

def nm_zr(cs, h):
  match cs:
    case Nil{}:
      {==}
    case _ch <> _tl:
      Empty.absurd({D1.zero_rest(_ch <> _tl) == True{} : Bool}, M2.false_true(h))

# nothing left: digits_end holds
law nm_de:
  for cs: List<&2, Char>
  for +h: {D1.no_more(cs) == True{} : Bool}
  {D1.digits_end(cs) == True{} : Bool}

def nm_de(cs, h):
  match cs:
    case Nil{}:
      {==}
    case _ch <> _tl:
      Empty.absurd({D1.digits_end(_ch <> _tl) == True{} : Bool}, M2.false_true(h))

# 45 is no digit 1-9
law d19_45:
  for +xx: U32
  for +h19: {D1.digit19(Chr{xx}) == True{} : Bool}
  {D1.is_cp(Chr{xx}, 45) == False{} : Bool}

def d19_45(xx, h19):
  bool_false(D1.is_cp(Chr{xx}, 45), hh => M2.false_true(Equal.trans(Bool, D1.digit19(Chr{45}), D1.digit19(Chr{xx}),
    True{},
    Equal.cong(U32, Bool, zz => D1.digit19(Chr{zz}), 45, xx, cp_eq(xx, 45, hh)), h19)))

# 45 is no digit
law dig_45:
  for +xx: U32
  for +hd: {D2.digit(Chr{xx}) == True{} : Bool}
  {D1.is_cp(Chr{xx}, 45) == False{} : Bool}

def dig_45(xx, hd):
  bool_false(D1.is_cp(Chr{xx}, 45), hh => M2.false_true(Equal.trans(Bool, D2.digit(Chr{45}), D2.digit(Chr{xx}),
    True{},
    Equal.cong(U32, Bool, zz => D2.digit(Chr{zz}), 45, xx, cp_eq(xx, 45, hh)), hd)))

# a decimal is a JSON number, once whether it starts with 0 is known
law num_of_dec:
  for +xx: U32
  for +tl: List<&2, Char>
  for zz: Bool
  for +ez: {D1.is_cp(Chr{xx}, 48) == zz : Bool}
  for +h: {D1.when(zz, D1.no_more(tl), D1.when(D1.digit19(Chr{xx}), D1.digits_end(tl),
    False{})) == True{} : Bool}
  {D1.number(Chr{xx} <> tl) == True{} : Bool}

def num_of_dec(xx, tl, zz, ez, h):
  match zz:
    case True{}:
      e48 = cp_eq(xx, 48, ez)
      %e48 : {D1.number(Chr{_} <> tl) == True{} : Bool}
      nm_zr(tl, h)
    case False{}:
      +d19 = when_c(D1.digit19(Chr{xx}), D1.digits_end(tl), h)
      c45 = Equal.sym(Bool, D1.is_cp(Chr{xx}, 45), False{}, d19_45(xx, d19))
      %c45 : {D1.when(_, D1.int_end(tl), D1.int_end(Chr{xx} <> tl)) == True{} : Bool}
      c48 = Equal.sym(Bool, D1.is_cp(Chr{xx}, 48), False{}, ez)
      %c48 : {D1.when(_, D1.zero_rest(tl), D1.when(D1.digit19(Chr{xx}), D1.digits_rest(tl),
        False{})) == True{} : Bool}
      e19 = Equal.sym(Bool, D1.digit19(Chr{xx}), True{}, d19)
      %e19 : {D1.when(_, D1.digits_rest(tl), False{}) == True{} : Bool}
      de_dr(tl, when_y(D1.digit19(Chr{xx}), D1.digits_end(tl), h))

# a decimal is a JSON number
law dec_number:
  for cs: List<&2, Char>
  for +h: {D1.decimal(cs) == True{} : Bool}
  {D1.number(cs) == True{} : Bool}

def dec_number(cs, h):
  match cs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, M2.false_true(h))
    case Chr{+xx} <> +tl:
      num_of_dec(xx, tl, D1.is_cp(Chr{xx}, 48), {==}, h)

# a when that is False first and one that is False last cannot both hold
law zr_nm.go:
  for dd: Bool
  for -xx: Bool
  for -yy: Bool
  for +hz: {D1.when(dd, False{}, xx) == True{} : Bool}
  for +hd: {D1.when(dd, yy, False{}) == True{} : Bool}
  Empty

def zr_nm.go(dd, _xx, _yy, hz, hd):
  match dd:
    case True{}:
      M2.false_true(hz)
    case False{}:
      M2.false_true(hd)

# zero_rest and digits_end together: nothing is left
law zr_nm:
  for cs: List<&2, Char>
  for +hz: {D1.zero_rest(cs) == True{} : Bool}
  for +hd: {D1.digits_end(cs) == True{} : Bool}
  {D1.no_more(cs) == True{} : Bool}

def zr_nm(cs, hz, hd):
  match cs:
    case Nil{}:
      {==}
    case +ch <> +tl:
      Empty.absurd({False{} == True{} : Bool}, zr_nm.go(D2.digit(ch), D1.when(D1.is_cp(ch, 46),
        D1.frac_body(tl),
        D1.when(D1.is_e(ch), D1.exp_body(tl), False{})), D1.digits_end(tl), hz, hd))

# a text that is all digits and a JSON number, once whether it starts with 0
# is known, is a decimal
law dec_of_num:
  for +xx: U32
  for +tl: List<&2, Char>
  for zz: Bool
  for +ez: {D1.is_cp(Chr{xx}, 48) == zz : Bool}
  for +hi: {D1.when(zz, D1.zero_rest(tl), D1.when(D1.digit19(Chr{xx}), D1.digits_rest(tl),
    False{})) == True{} : Bool}
  for +de: {D1.digits_end(tl) == True{} : Bool}
  {D1.decimal(Chr{xx} <> tl) == True{} : Bool}

def dec_of_num(xx, tl, zz, ez, hi, de):
  match zz:
    case True{}:
      e48 = Equal.sym(Bool, D1.is_cp(Chr{xx}, 48), True{}, ez)
      %e48 : {D1.when(_, D1.no_more(tl), D1.when(D1.digit19(Chr{xx}), D1.digits_end(tl),
        False{})) == True{} : Bool}
      zr_nm(tl, hi, de)
    case False{}:
      e48 = Equal.sym(Bool, D1.is_cp(Chr{xx}, 48), False{}, ez)
      %e48 : {D1.when(_, D1.no_more(tl), D1.when(D1.digit19(Chr{xx}), D1.digits_end(tl),
        False{})) == True{} : Bool}
      e19 = Equal.sym(Bool, D1.digit19(Chr{xx}), True{}, when_c(D1.digit19(Chr{xx}), D1.digits_rest(tl), hi))
      %e19 : {D1.when(_, D1.digits_end(tl), False{}) == True{} : Bool}
      de

# a JSON number that is all digits is a decimal
law num_dec:
  for +cs: List<&2, Char>
  for +hn: {D1.number(cs) == True{} : Bool}
  for +hd: {D1.digits_end(cs) == True{} : Bool}
  {D1.decimal(cs) == True{} : Bool}

def num_dec(cs, hn, hd):
  match cs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, M2.false_true(hn))
    case Chr{+xx} <> +tl:
      c45 = dig_45(xx, when_c(D2.digit(Chr{xx}), D1.digits_end(tl), hd))
      hi = Equal.trans(Bool, D1.int_end(Chr{xx} <> tl), D1.number(Chr{xx} <> tl), True{},
        Equal.cong(Bool, Bool, zz => D1.when(zz, D1.int_end(tl), D1.int_end(Chr{xx} <> tl)), False{},
          D1.is_cp(Chr{xx}, 45), Equal.sym(Bool, D1.is_cp(Chr{xx}, 45), False{}, c45)), hn)
      dec_of_num(xx, tl, D1.is_cp(Chr{xx}, 48), {==}, hi, when_y(D2.digit(Chr{xx}), D1.digits_end(tl), hd))

# at least b + 1 is at least b
law ge_pred:
  for aa: Nat
  for bb: Nat
  for +h: {Cmp.is_ge(Nat.cmp(aa, 1n+bb)) == True{} : Bool}
  {Cmp.is_ge(Nat.cmp(aa, bb)) == True{} : Bool}

def ge_pred(aa, bb, h):
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+_bp:
      Empty.absurd({False{} == True{} : Bool}, M2.false_true(h))
    case 1n+_ap 0n:
      {==}
    case 1n+ap 1n+bp:
      ge_pred(ap, bp, h)

# a digit 1-9 is a digit
law d19_dig:
  for +xx: U32
  for +h19: {D1.digit19(Chr{xx}) == True{} : Bool}
  {D2.digit(Chr{xx}) == True{} : Bool}

def d19_dig(xx, h19):
  Equal.trans(Bool, Bool.and(Cmp.is_ge(U32.cmp(xx, 48)), Cmp.is_le(U32.cmp(xx, 57))),
    Bool.and(True{}, Cmp.is_le(U32.cmp(xx, 57))), True{},
    Equal.cong(Bool, Bool, zz => Bool.and(zz, Cmp.is_le(U32.cmp(xx, 57))), Cmp.is_ge(U32.cmp(xx, 48)), True{},
      Equal.trans(Bool, Cmp.is_ge(U32.cmp(xx, 48)), Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 48n)), True{},
        Equal.cong(Cmp, Bool, zz => Cmp.is_ge(zz), U32.cmp(xx, 48), Nat.cmp(U32.to_nat(xx), 48n), u_cmp(xx, 48)),
        ge_pred(U32.to_nat(xx), 48n, Equal.trans(Bool, Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 49n)), Cmp.is_ge(U32.cmp(xx,
          49)),
          True{},
          Equal.cong(Cmp, Bool, zz => Cmp.is_ge(zz), Nat.cmp(U32.to_nat(xx), 49n), U32.cmp(xx, 49),
            Equal.sym(Cmp, U32.cmp(xx, 49), Nat.cmp(U32.to_nat(xx), 49n), u_cmp(xx, 49))),
          M2.and_left(Cmp.is_ge(U32.cmp(xx, 49)), Cmp.is_le(U32.cmp(xx, 57)), h19))))),
    M2.and_right(Cmp.is_ge(U32.cmp(xx, 49)), Cmp.is_le(U32.cmp(xx, 57)), h19))

# a decimal is all digits, once whether it starts with 0 is known
law dec_digits_at:
  for +xx: U32
  for +tl: List<&2, Char>
  for zz: Bool
  for +ez: {D1.is_cp(Chr{xx}, 48) == zz : Bool}
  for +h: {D1.when(zz, D1.no_more(tl), D1.when(D1.digit19(Chr{xx}), D1.digits_end(tl),
    False{})) == True{} : Bool}
  {D1.digits_end(Chr{xx} <> tl) == True{} : Bool}

def dec_digits_at(xx, tl, zz, ez, h):
  match zz:
    case True{}:
      e48 = cp_eq(xx, 48, ez)
      %e48 : {D1.digits_end(Chr{_} <> tl) == True{} : Bool}
      nm_de(tl, h)
    case False{}:
      dg = Equal.sym(Bool, D2.digit(Chr{xx}), True{}, d19_dig(xx, when_c(D1.digit19(Chr{xx}), D1.digits_end(tl),
        h)))
      %dg : {D1.when(_, D1.digits_end(tl), False{}) == True{} : Bool}
      when_y(D1.digit19(Chr{xx}), D1.digits_end(tl), h)

# a decimal is all digits
law dec_digits:
  for cs: List<&2, Char>
  for +h: {D1.decimal(cs) == True{} : Bool}
  {D1.digits_end(cs) == True{} : Bool}

def dec_digits(cs, h):
  match cs:
    case Nil{}:
      Empty.absurd({True{} == True{} : Bool}, M2.false_true(h))
    case Chr{+xx} <> +tl:
      dec_digits_at(xx, tl, D1.is_cp(Chr{xx}, 48), {==}, h)

# laws/AsU32ReadsPlainDigits.bend: as_u32 of num

# U32.read of a JSON number, once whether it is all digits is known
law as_u32_digits:
  for +uu: Unit
  for +ss: String
  for +hn: {D1.number(String.to_list(ss)) == True{} : Bool}
  for de: Bool
  for +ede: {D1.digits_end(String.to_list(ss)) == de : Bool}
  {Laws.u32_nat(U32.read.go(ss, 0)) == Laws.dec_u32(String.to_list(ss)) : Maybe<&2, Nat>}

def as_u32_digits(uu, ss, hn, de, ede):
  match de:
    case True{}:
      ee = Equal.sym(Bool, D1.decimal(String.to_list(ss)), True{}, num_dec(String.to_list(ss), hn, ede))
      %ee : {Laws.u32_nat(U32.read.go(ss, 0)) == Laws.nat_if(Bool.and(_, Laws.fits(32n,
        Laws.dec_val(String.to_list(ss), 0n))),
        Laws.dec_val(String.to_list(ss), 0n)) : Maybe<&2, Nat>}
      read_all(uu, ss, 0, ede)
    case False{}:
      ee = Equal.sym(Bool, D1.decimal(String.to_list(ss)), False{}, bool_false(D1.decimal(String.to_list(ss)),
        hh => M1.true_false(
        Equal.trans(Bool, True{}, D1.digits_end(String.to_list(ss)), False{},
          Equal.sym(Bool, D1.digits_end(String.to_list(ss)), True{}, dec_digits(String.to_list(ss), hh)), ede))))
      %ee : {Laws.u32_nat(U32.read.go(ss, 0)) == Laws.nat_if(Bool.and(_, Laws.fits(32n,
        Laws.dec_val(String.to_list(ss), 0n))),
        Laws.dec_val(String.to_list(ss), 0n)) : Maybe<&2, Nat>}
      Equal.cong(Maybe<&2, U32>, Maybe<&2, Nat>, mm => Laws.u32_nat(mm), U32.read.go(ss, 0), None{},
        read_bad(uu, ss, 0, ede))

# U32.read of a JSON number
law as_u32_read:
  for +uu: Unit
  for txt: String
  for +hn: {D1.number(String.to_list(txt)) == True{} : Bool}
  {Laws.u32_nat(U32.read(txt)) == Laws.dec_u32(String.to_list(txt)) : Maybe<&2, Nat>}

def as_u32_read(uu, txt, hn):
  match txt:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      as_u32_digits(uu, SCon{hh, tt}, hn, D1.digits_end(String.to_list(SCon{hh, tt})), {==})

# as_u32 of num, once whether the text is a JSON number is known
law as_u32_top:
  for +uu: Unit
  for +txt: String
  for ok: Bool
  for +eok: {V.num.ok(txt) == ok : Bool}
  {Laws.u32_nat(V.as_u32(V.num.go(txt, ok))) == Laws.dec_u32(String.to_list(txt)) : Maybe<&2, Nat>}

def as_u32_top(uu, txt, ok, eok):
  match ok:
    case True{}:
      as_u32_read(uu, txt, Equal.trans(Bool, D1.number(String.to_list(txt)), V.num.ok(txt), True{},
        Equal.sym(Bool, V.num.ok(txt), D1.number(String.to_list(txt)), L1.num_grammar(txt)), eok))
    case False{}:
      ee = Equal.sym(Bool, D1.decimal(String.to_list(txt)), False{}, bool_false(D1.decimal(String.to_list(txt)),
        hh => M1.true_false(Equal.trans(Bool, True{}, D1.number(String.to_list(txt)), False{},
          Equal.sym(Bool, D1.number(String.to_list(txt)), True{}, dec_number(String.to_list(txt), hh)),
          Equal.trans(Bool, D1.number(String.to_list(txt)), V.num.ok(txt), False{},
            Equal.sym(Bool, V.num.ok(txt), D1.number(String.to_list(txt)), L1.num_grammar(txt)), eok)))))
      %ee : {Laws.u32_nat(V.as_u32(V.num.go(txt, False{}))) == Laws.nat_if(Bool.and(_,
        Laws.fits(32n, Laws.dec_val(String.to_list(txt), 0n))), Laws.dec_val(String.to_list(txt), 0n)) : Maybe<&2, Nat>}
      {==}

def Laws.as_u32_num(txt):
  as_u32_top(Unit{}, txt, V.num.ok(txt), {==})

def Laws.u32_nat_inj(aa, bb, h):
  M5.ueq(aa, bb, Equal.trans(Bool, Cmp.is_eq(U32.cmp(aa, bb)), Cmp.is_eq(Nat.cmp(U32.to_nat(aa), U32.to_nat(bb))),
      True{},
    Equal.cong(Cmp, Bool, zz => Cmp.is_eq(zz), U32.cmp(aa, bb), Nat.cmp(U32.to_nat(aa), U32.to_nat(bb)), u_cmp(aa, bb)),
    Equal.trans(Bool, Cmp.is_eq(Nat.cmp(U32.to_nat(aa), U32.to_nat(bb))), Cmp.is_eq(Nat.cmp(U32.to_nat(bb),
      U32.to_nat(bb))), True{},
      Equal.cong(Nat, Bool, zz => Cmp.is_eq(Nat.cmp(zz, U32.to_nat(bb))), U32.to_nat(aa), U32.to_nat(bb), h),
      Equal.cong(Cmp, Bool, zz => Cmp.is_eq(zz), Nat.cmp(U32.to_nat(bb), U32.to_nat(bb)), EQ{},
        nat_cmp_refl(U32.to_nat(bb))))))
