# addition and order on natural numbers
import Base
import ./LexemeOrder.bend as M1

# laws/AsU32ReadsPlainDigits.bend: Nat arithmetic, for as_u32's U32 steps

# the predecessor of a Nat
def npred(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+(+pp):
      pp

# adding 0 on the right
law nat_add_zero:
  for +aa: Nat
  {Nat.add(aa, 0n) == aa : Nat}

def nat_add_zero(aa):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 0n), pp, nat_add_zero(pp))

# adding one more on the right
law nat_add_succ:
  for +aa: Nat
  for +bb: Nat
  {Nat.add(aa, 1n+bb) == 1n+Nat.add(aa, bb) : Nat}

def nat_add_succ(aa, bb):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 1n+bb), 1n+Nat.add(pp, bb), nat_add_succ(pp, bb))

# addition commutes
law nat_add_comm:
  for +aa: Nat
  for +bb: Nat
  {Nat.add(aa, bb) == Nat.add(bb, aa) : Nat}

def nat_add_comm(aa, bb):
  match aa:
    case 0n:
      Equal.sym(Nat, Nat.add(bb, 0n), bb, nat_add_zero(bb))
    case 1n+(+pp):
      Equal.trans(Nat, 1n+Nat.add(pp, bb), 1n+Nat.add(bb, pp), Nat.add(bb, 1n+pp),
        Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, bb), Nat.add(bb, pp), nat_add_comm(pp, bb)),
        Equal.sym(Nat, Nat.add(bb, 1n+pp), 1n+Nat.add(bb, pp), nat_add_succ(bb, pp)))

# addition associates
law nat_add_assoc:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  {Nat.add(Nat.add(aa, bb), cc) == Nat.add(aa, Nat.add(bb, cc)) : Nat}

def nat_add_assoc(aa, bb, cc):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(Nat.add(pp, bb), cc), Nat.add(pp, Nat.add(bb, cc)),
        nat_add_assoc(pp, bb, cc))

# the first two of three addends swap
law nat_add_lcomm:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  {Nat.add(aa, Nat.add(bb, cc)) == Nat.add(bb, Nat.add(aa, cc)) : Nat}

def nat_add_lcomm(aa, bb, cc):
  Equal.trans(Nat, Nat.add(aa, Nat.add(bb, cc)), Nat.add(Nat.add(aa, bb), cc), Nat.add(bb, Nat.add(aa, cc)),
    Equal.sym(Nat, Nat.add(Nat.add(aa, bb), cc), Nat.add(aa, Nat.add(bb, cc)), nat_add_assoc(aa, bb, cc)),
    Equal.trans(Nat, Nat.add(Nat.add(aa, bb), cc), Nat.add(Nat.add(bb, aa), cc), Nat.add(bb, Nat.add(aa, cc)),
      Equal.cong(Nat, Nat, xx => Nat.add(xx, cc), Nat.add(aa, bb), Nat.add(bb, aa), nat_add_comm(aa, bb)),
      nat_add_assoc(bb, aa, cc)))

# a common left addend cancels
law nat_add_cancel:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  for h: {Nat.add(aa, bb) == Nat.add(aa, cc) : Nat}
  {bb == cc : Nat}

def nat_add_cancel(aa, bb, cc, h):
  match aa:
    case 0n:
      h
    case 1n+(+pp):
      nat_add_cancel(pp, bb, cc, Equal.cong(Nat, Nat, xx => npred(xx), 1n+Nat.add(pp, bb), 1n+Nat.add(pp, cc), h))

# doubling is adding to itself
law nat_double:
  for +aa: Nat
  {Nat.double(aa) == Nat.add(aa, aa) : Nat}

def nat_double(aa):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.trans(Nat, 2n+Nat.double(pp), 2n+Nat.add(pp, pp), 1n+Nat.add(pp, 1n+pp),
        Equal.cong(Nat, Nat, xx => 2n+xx, Nat.double(pp), Nat.add(pp, pp), nat_double(pp)),
        Equal.cong(Nat, Nat, xx => 1n+xx, 1n+Nat.add(pp, pp), Nat.add(pp, 1n+pp),
          Equal.sym(Nat, Nat.add(pp, 1n+pp), 1n+Nat.add(pp, pp), nat_add_succ(pp, pp))))

# doubling a sum doubles each addend
law nat_double_add:
  for +aa: Nat
  for +bb: Nat
  {Nat.double(Nat.add(aa, bb)) == Nat.add(Nat.double(aa), Nat.double(bb)) : Nat}

def nat_double_add(aa, bb):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, xx => 2n+xx, Nat.double(Nat.add(pp, bb)), Nat.add(Nat.double(pp), Nat.double(bb)),
        nat_double_add(pp, bb))

# a less 0 is a
law nat_sub_zero:
  for +aa: Nat
  {Nat.sub(aa, 0n) == aa : Nat}

def nat_sub_zero(aa):
  match aa:
    case 0n:
      {==}
    case 1n+_pp:
      {==}

# the witness of a < b: b is a, one, and b - (a + 1)
law nat_lt_ex:
  for +aa: Nat
  for +bb: Nat
  for h: {Nat.is_lt(aa, bb) == True{} : Bool}
  {1n+Nat.add(aa, Nat.sub(bb, 1n+aa)) == bb : Nat}

def nat_lt_ex(aa, bb, h):
  match aa bb:
    case 0n 0n:
      Empty.absurd({1n == 0n : Nat}, M1.false_true(h))
    case 0n 1n+(+bp):
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.sub(bp, 0n), bp, nat_sub_zero(bp))
    case 1n+_ap 0n:
      Empty.absurd({1n+Nat.add(aa, Nat.sub(0n, 1n+aa)) == 0n : Nat}, M1.false_true(h))
    case 1n+(+ap) 1n+(+bp):
      Equal.cong(Nat, Nat, xx => 1n+xx, 1n+Nat.add(ap, Nat.sub(bp, 1n+ap)), bp, nat_lt_ex(ap, bp, h))

# 2^nn
def pow2(nn: Nat) -> Nat:
  match nn:
    case 0n:
      1n
    case 1n+pp:
      Nat.double(pow2(pp))

# 2^nn once uu is known. The checker expands a closed Nat to unary to compare
# it, and 2^32 is too large for that, so a lemma about U32s takes a unit uu
# and names 2^32 as pow2u(32n, uu), which stays unexpanded
def pow2u(nn: Nat, uu: Unit) -> Nat:
  match uu:
    case Unit{}:
      pow2(nn)

# below y, twice x is below twice y
law nat_lt_dbl:
  for +xx: Nat
  for +yy: Nat
  for h: {Nat.is_lt(xx, yy) == True{} : Bool}
  {Nat.is_lt(Nat.double(xx), Nat.double(yy)) == True{} : Bool}

def nat_lt_dbl(xx, yy, h):
  match xx yy:
    case 0n 0n:
      h
    case 0n 1n+_yp:
      {==}
    case 1n+_xp 0n:
      Empty.absurd({Nat.is_lt(Nat.double(xx), 0n) == True{} : Bool}, M1.false_true(h))
    case 1n+(+xp) 1n+(+yp):
      nat_lt_dbl(xp, yp, h)

# below y, twice x and one is below twice y
law nat_lt_dbl1:
  for +xx: Nat
  for +yy: Nat
  for h: {Nat.is_lt(xx, yy) == True{} : Bool}
  {Nat.is_lt(1n+Nat.double(xx), Nat.double(yy)) == True{} : Bool}

def nat_lt_dbl1(xx, yy, h):
  match xx yy:
    case 0n 0n:
      h
    case 0n 1n+_yp:
      {==}
    case 1n+_xp 0n:
      Empty.absurd({Nat.is_lt(1n+Nat.double(xx), 0n) == True{} : Bool}, M1.false_true(h))
    case 1n+(+xp) 1n+(+yp):
      nat_lt_dbl1(xp, yp, h)

# a word of nn bits is below 2^nn
law w_bound:
  for +nn: Nat
  for ww: Word(nn)
  {Nat.is_lt(Word.to_nat(nn, ww), pow2(nn)) == True{} : Bool}

def w_bound(nn, ww):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match ww:
        case WCon{False{}, +tt}:
          nat_lt_dbl(Word.to_nat(pp, tt), pow2(pp), w_bound(pp, tt))
        case WCon{True{}, +tt}:
          nat_lt_dbl1(Word.to_nat(pp, tt), pow2(pp), w_bound(pp, tt))

# w_bound, with 2^nn named through uu
law w_bound_u:
  for +nn: Nat
  for uu: Unit
  for ww: Word(nn)
  {Nat.is_lt(Word.to_nat(nn, ww), pow2u(nn, uu)) == True{} : Bool}

def w_bound_u(nn, uu, ww):
  match uu:
    case Unit{}:
      w_bound(nn, ww)

# a U32 is below 2^32
law u_bound:
  for +uu: Unit
  for aa: U32
  {Nat.is_lt(U32.to_nat(aa), pow2u(32n, uu)) == True{} : Bool}

def u_bound(uu, aa):
  match aa:
    case U32{ww}:
      w_bound_u(32n, uu, ww)
