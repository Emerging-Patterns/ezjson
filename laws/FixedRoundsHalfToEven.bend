# The digits are cut after the `n`-th fraction place: exactly `n` fraction
# digits are kept, `0`s past the last fraction digit, and the rest are
# dropped. The kept digits go up by one in the last kept place exactly when
# the first dropped digit is above `5`; or is `5` and a later dropped digit is
# not `0`; or is `5`, every later dropped digit is `0`, and the last kept
# digit is odd (a tie goes to the even neighbour, and no kept digit at all
# counts as an even `0`). No dropped digit, or a first dropped digit below
# `5`, keeps the digits as they are. Going up by one makes a last `9` a `0`
# and carries, and all `9`s become `0`s under a new leading `1`
import Base
import ../src/fixed.bend as F

# a character's place against `5`
def vs5(+ch: Char) -> Cmp:
  U32.cmp(Char.to_u32(ch), 53)

# LAW: rounding cuts the fraction after nn places, joins the kept digits
# last first, and adds one when the dropped digits say so
law round_cut:
  for +nn: Nat
  for +left: String
  for +right: String
  for +kept: String
  for +dropped: String
  for +h: {F.pad(nn, right) == (kept, dropped) : String & String}
  {F.round(nn, F.Dec{left, right})
    == F.bump(F.round.up(dropped, String.reverse.go(kept, left)),
      String.reverse.go(kept, left)) : String}

# LAW: the kept fraction digits are exactly nn
law pad_width:
  for +nn: Nat
  for +right: String
  {String.length(Pair.fst(String, String, F.pad(nn, right))) == nn : Nat}

# LAW: no place kept keeps nothing and drops every fraction digit
law pad_none:
  for +right: String
  {F.pad(0n, right) == ("", right) : String & String}

# LAW: a kept place takes the next fraction digit
law pad_digit:
  for +mm: Nat
  for +ch: Char
  for +tl: String
  {F.pad(1n+mm, SCon{ch, tl}) == F.cut.put(ch, F.pad(mm, tl))
    : String & String}

# LAW: a kept place past the last fraction digit is a 0
law pad_past:
  for +mm: Nat
  {F.pad(1n+mm, "") == F.cut.put('0', F.pad(mm, "")) : String & String}

# LAW: no dropped digit: no rounding
law up_exact:
  for +kept: String
  {F.round.up("", kept) == False{} : Bool}

# LAW: a first dropped digit below 5 rounds down
law up_below:
  for +dd: Char
  for +rest: String
  for +kept: String
  for +h: {vs5(dd) == LT{} : Cmp}
  {F.round.up(SCon{dd, rest}, kept) == False{} : Bool}

# LAW: a first dropped digit above 5 rounds up
law up_above:
  for +dd: Char
  for +rest: String
  for +kept: String
  for +h: {vs5(dd) == GT{} : Cmp}
  {F.round.up(SCon{dd, rest}, kept) == True{} : Bool}

# LAW: a first dropped digit of 5 with a later nonzero dropped digit is past
# half, and rounds up
law up_past_half:
  for +dd: Char
  for +rest: String
  for +kept: String
  for +h_d: {vs5(dd) == EQ{} : Cmp}
  for +h_r: {F.nonzero(rest) == True{} : Bool}
  {F.round.up(SCon{dd, rest}, kept) == True{} : Bool}

# LAW: an exact half rounds up exactly when the last kept digit is odd
law up_tie:
  for +dd: Char
  for +rest: String
  for +last: Char
  for +kept: String
  for +h_d: {vs5(dd) == EQ{} : Cmp}
  for +h_r: {F.nonzero(rest) == False{} : Bool}
  {F.round.up(SCon{dd, rest}, SCon{last, kept})
    == U32.is_eq(U32.mod(Char.to_u32(last), 2), 1) : Bool}

# LAW: an exact half with no kept digit (an empty integer part and no
# places) counts as even 0, and rounds down
law up_tie_none:
  for +dd: Char
  for +rest: String
  for +h_d: {vs5(dd) == EQ{} : Cmp}
  for +h_r: {F.nonzero(rest) == False{} : Bool}
  {F.round.up(SCon{dd, rest}, "") == False{} : Bool}

# LAW: dropped digits that are all 0 are not past half
law nonzero_zeros:
  for +kk: Nat
  {F.nonzero(String.repeat("0", kk)) == False{} : Bool}

# LAW: a digit other than 0 anywhere among the dropped digits is past half
law nonzero_digit:
  for +pre: String
  for +ch: Char
  for +post: String
  for +h: {Char.is_eq(ch, '0') == False{} : Bool}
  {F.nonzero(pre ++ SCon{ch, post}) == True{} : Bool}

# LAW: rounding up adds one, rounding down keeps the digits
law bump_up:
  for +kept: String
  {F.bump(True{}, kept) == F.inc(kept) : String}

# LAW: rounding down keeps the digits
law bump_down:
  for +kept: String
  {F.bump(False{}, kept) == kept : String}

# LAW: adding one to a last digit other than 9 makes it the next digit
law inc_digit:
  for +ch: Char
  for +tl: String
  for +h: {Char.is_eq(ch, '9') == False{} : Bool}
  {F.inc(SCon{ch, tl}) == SCon{Char.from_u32(U32.add(Char.to_u32(ch), 1)), tl}
    : String}

# LAW: adding one to a last digit 9 makes it 0 and carries one
law inc_nine:
  for +tl: String
  {F.inc(SCon{'9', tl}) == SCon{'0', F.inc(tl)} : String}

# LAW: adding one to all 9s makes them 0s and a new leading 1
law inc_nines:
  for +kk: Nat
  {F.inc(String.repeat("9", kk)) == String.repeat("0", kk) ++ "1" : String}
