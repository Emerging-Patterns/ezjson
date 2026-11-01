# An unsigned text is cut at its first `e` or `E` into a mantissa and an
# exponent (no mark: the exponent is empty), and the mantissa at its first `.`
# into integer and fraction digits (no point: the fraction is empty). An
# exponent's leading `-` makes it negative, a leading `+` is dropped, and any
# other exponent is positive and keeps every character. The exponent's digits
# are read most significant first as the natural number `k` (empty: 0). The
# integer digits, last first, and the fraction digits stand around the point,
# and the point moves `k` places right for a positive exponent and left for a
# negative one, one place a step: a move right carries the first fraction
# digit before the point, or a `0` when there is none, and a move left carries
# the last integer digit after the point, or a `0` when there is none; a move
# right then left, or left then right, gives the same digits back. So `1e-05`
# is `0.00001` and `2.5e1` is `25`
import Base
import ../src/fixed.bend as F
import ./defs/CursorAndNumberRules.bend as D1

# --- fixed decimals (JSON-FIX) ---

# no character of the text is an exponent mark, `e` or `E`
def no_e(+txt: String) -> Bool:
  match txt:
    case SNil{}:
      True{}
    case SCon{+ch, +tl}:
      D1.when(F.mark.e(ch), False{}, no_e(tl))

# no character of the text is a decimal point
def no_dot(+txt: String) -> Bool:
  match txt:
    case SNil{}:
      True{}
    case SCon{+ch, +tl}:
      D1.when(F.mark.dot(ch), False{}, no_dot(tl))

# LAW: an unsigned text is split, its point moved, rounded at nn places and
# written
law unsigned_steps:
  for +txt: String
  for +nn: Nat
  {F.unsigned(txt, nn) == F.write(nn, F.round(nn, F.place(F.parts(txt))))
    : String}

# LAW: a text with an exponent mark is cut at the first one: the mantissa
# before it, the exponent after it
law parts_exp:
  for +mant: String
  for +ch: Char
  for +exp: String
  for +h_m: {no_e(mant) == True{} : Bool}
  for +h_c: {F.mark.e(ch) == True{} : Bool}
  {F.parts(mant ++ SCon{ch, exp}) == (F.cut.dot(mant), F.esign(exp))
    : (String & String) & (Bool & String)}

# LAW: a text with no exponent mark is all mantissa, with exponent 0
law parts_plain:
  for +mant: String
  for +h_m: {no_e(mant) == True{} : Bool}
  {F.parts(mant) == (F.cut.dot(mant), (False{}, ""))
    : (String & String) & (Bool & String)}

# LAW: a mantissa with a point is cut at the first one: the integer digits
# before it, the fraction digits after it
law mant_dot:
  for +int: String
  for +frac: String
  for +h_i: {no_dot(int) == True{} : Bool}
  {F.cut.dot(int ++ "." ++ frac) == (int, frac) : String & String}

# LAW: a mantissa with no point is all integer digits
law mant_int:
  for +int: String
  for +h_i: {no_dot(int) == True{} : Bool}
  {F.cut.dot(int) == (int, "") : String & String}

# LAW: an exponent's leading minus makes it negative
law esign_minus:
  for +exp: String
  {F.esign("-" ++ exp) == (True{}, exp) : Bool & String}

# LAW: an exponent's leading plus is dropped
law esign_plus:
  for +exp: String
  {F.esign("+" ++ exp) == (False{}, exp) : Bool & String}

# LAW: an exponent with no sign is positive and keeps every digit
law esign_digits:
  for +ch: Char
  for +tl: String
  for +h_m: {Char.is_eq(ch, '-') == False{} : Bool}
  for +h_p: {Char.is_eq(ch, '+') == False{} : Bool}
  {F.esign(SCon{ch, tl}) == (False{}, SCon{ch, tl}) : Bool & String}

# LAW: the integer digits, last first, and the fraction digits stand around
# the point, which the exponent moves
law place_parts:
  for +int: String
  for +frac: String
  for +neg: Bool
  for +exp: String
  {F.place(((int, frac), (neg, exp)))
    == F.move(neg, F.nat(exp), F.Dec{String.reverse(int), frac}) : F.Dec}

# LAW: an exponent's digits are read from 0
law nat_start:
  for +exp: String
  {F.nat(exp) == F.nat.go(exp, 0n) : Nat}

# LAW: reading no more digits leaves the value read
law nat_end:
  for +acc: Nat
  {F.nat.go("", acc) == acc : Nat}

# LAW: one more digit at the end is ten times the value so far plus that
# digit: most significant first
law nat_snoc:
  for +exp: String
  for +ch: Char
  for +acc: Nat
  {F.nat.go(exp ++ SCon{ch, SNil{}}, acc)
    == Nat.add(Nat.mul(F.nat.go(exp, acc), 10n),
      U32.to_nat(U32.sub(Char.to_u32(ch), 48))) : Nat}

# LAW: a positive exponent moves the point right, a negative one left
law move_right:
  for +kk: Nat
  for +dec: F.Dec
  {F.move(False{}, kk, dec) == F.ups(kk, dec) : F.Dec}

# LAW: a negative exponent moves the point left
law move_left:
  for +kk: Nat
  for +dec: F.Dec
  {F.move(True{}, kk, dec) == F.downs(kk, dec) : F.Dec}

# LAW: moving the point no places right leaves it
law ups_zero:
  for +dec: F.Dec
  {F.ups(0n, dec) == dec : F.Dec}

# LAW: moving the point k + 1 places right is one move, then k
law ups_succ:
  for +kk: Nat
  for +dec: F.Dec
  {F.ups(1n+kk, dec) == F.ups(kk, F.up(dec)) : F.Dec}

# LAW: moving the point no places left leaves it
law downs_zero:
  for +dec: F.Dec
  {F.downs(0n, dec) == dec : F.Dec}

# LAW: moving the point k + 1 places left is one move, then k
law downs_succ:
  for +kk: Nat
  for +dec: F.Dec
  {F.downs(1n+kk, dec) == F.downs(kk, F.down(dec)) : F.Dec}

# LAW: one move right carries the first fraction digit before the point
law up_digit:
  for +left: String
  for +ch: Char
  for +tl: String
  {F.up(F.Dec{left, SCon{ch, tl}}) == F.Dec{SCon{ch, left}, tl} : F.Dec}

# LAW: one move right with no fraction digit carries a 0 before the point
law up_zero:
  for +left: String
  {F.up(F.Dec{left, ""}) == F.Dec{SCon{'0', left}, ""} : F.Dec}

# LAW: one move left carries the last integer digit after the point
law down_digit:
  for +ch: Char
  for +tl: String
  for +right: String
  {F.down(F.Dec{SCon{ch, tl}, right}) == F.Dec{tl, SCon{ch, right}} : F.Dec}

# LAW: one move left with no integer digit carries a 0 after the point
law down_zero:
  for +right: String
  {F.down(F.Dec{"", right}) == F.Dec{"", SCon{'0', right}} : F.Dec}

# LAW: a move right then left gives back the digits around the point
law up_down:
  for +left: String
  for +ch: Char
  for +tl: String
  {F.down(F.up(F.Dec{left, SCon{ch, tl}})) == F.Dec{left, SCon{ch, tl}}
    : F.Dec}

# LAW: a move left then right gives back the digits around the point
law down_up:
  for +ch: Char
  for +tl: String
  for +right: String
  {F.up(F.down(F.Dec{SCon{ch, tl}, right})) == F.Dec{SCon{ch, tl}, right}
    : F.Dec}
