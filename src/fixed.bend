# src/fixed: a JSON number's text written with a fixed count of decimals.
# The digits are rounded half to even as decimal digits, never through a
# binary float. The text is split at its `e` (or `E`) and its `.`; the
# exponent moves the point; the digits past the last kept place decide
# whether the kept ones go up by one; the integer part loses its leading
# zeros. A `-` is kept even when the rounded value is zero, as C's printf
# and Python's `'%.Nf'` keep it.
import Base
import ./value.bend as V

# where a number's point is: the digits before it, last digit first, and the
# digits after it
type Dec is Data:
  Dec{left: String, right: String}

# --- splitting the text ---

# an exponent mark, `e` or `E`
def mark.e(+ch: Char) -> Bool:
  Bool.or(Char.is_eq(ch, 'e'), Char.is_eq(ch, 'E'))

# a decimal point
def mark.dot(+ch: Char) -> Bool:
  Char.is_eq(ch, '.')

# put a character before the first of a pair
def cut.put(ch: Char, pair: String & String) -> String & String:
  (a, b) = pair
  (SCon{ch, a}, b)

# at a mark the cut is made; any other character is kept before it
def cut.at(
  hit: Bool,
  ch: Char,
  after: String,
  more: Unit -> String & String
) -> String & String:
  match hit:
    case True{}:
      ("", after)
    case False{}:
      cut.put(ch, more(Unit{}))

# a text cut at its first exponent mark: what is before it, and after it
def cut.e(txt: String) -> String & String:
  match txt:
    case SNil{}:
      ("", "")
    case SCon{+hd, +tl}:
      cut.at(mark.e(hd), hd, tl, _u => cut.e(tl))

# a text cut at its first decimal point: what is before it, and after it
def cut.dot(txt: String) -> String & String:
  match txt:
    case SNil{}:
      ("", "")
    case SCon{+hd, +tl}:
      cut.at(mark.dot(hd), hd, tl, _u => cut.dot(tl))

# an exponent's sign and digits: `-` makes it negative, `+` is dropped
def esign.at(minus: Bool, plus: Bool, ch: Char, tl: String) -> Bool & String:
  match minus plus:
    case True{} _:
      (True{}, tl)
    case False{} True{}:
      (False{}, tl)
    case False{} False{}:
      (False{}, SCon{ch, tl})

# an exponent's sign and digits
def esign(txt: String) -> Bool & String:
  match txt:
    case SNil{}:
      (False{}, "")
    case SCon{+hd, tl}:
      esign.at(Char.is_eq(hd, '-'), Char.is_eq(hd, '+'), hd, tl)

# the parts of a text cut at its exponent mark
def parts.of(cut: String & String) -> (String & String) & (Bool & String):
  (mant, exp) = cut
  (cut.dot(mant), esign(exp))

# an unsigned number's parts: its integer and fraction digits, and its
# exponent's sign and digits
def parts(txt: String) -> (String & String) & (Bool & String):
  parts.of(cut.e(txt))

# --- the exponent ---

# a digit's value
def digit.nat(ch: Char) -> Nat:
  U32.to_nat(U32.sub(Char.to_u32(ch), 48))

# decimal digits read onto acc, most significant first
def nat.go(txt: String, acc: Nat) -> Nat:
  match txt:
    case SNil{}:
      acc
    case SCon{hd, tl}:
      nat.go(tl, Nat.add(Nat.mul(acc, 10n), digit.nat(hd)))

# decimal digits' value
def nat(txt: String) -> Nat:
  nat.go(txt, 0n)

# the point one place right: the first fraction digit, or a 0 past the
# last, moves before the point
def up(dec: Dec) -> Dec:
  match dec:
    case Dec{left, right}:
      match right:
        case SNil{}:
          Dec{SCon{'0', left}, ""}
        case SCon{hd, tl}:
          Dec{SCon{hd, left}, tl}

# the point one place left: the last integer digit, or a 0 before the
# first, moves after the point
def down(dec: Dec) -> Dec:
  match dec:
    case Dec{left, right}:
      match left:
        case SNil{}:
          Dec{"", SCon{'0', right}}
        case SCon{hd, tl}:
          Dec{tl, SCon{hd, right}}

# the point `kk` places right
def ups(kk: Nat, dec: Dec) -> Dec:
  match kk:
    case 0n:
      dec
    case 1n+j:
      ups(j, up(dec))

# the point `kk` places left
def downs(kk: Nat, dec: Dec) -> Dec:
  match kk:
    case 0n:
      dec
    case 1n+j:
      downs(j, down(dec))

# the digits with the point moved by the exponent
def move(neg: Bool, kk: Nat, dec: Dec) -> Dec:
  match neg:
    case False{}:
      ups(kk, dec)
    case True{}:
      downs(kk, dec)

# the parts as digits around the point, the point moved by the exponent
def place(pts: (String & String) & (Bool & String)) -> Dec:
  ((int, frac), (neg, exp)) = pts
  move(neg, nat(exp), Dec{String.reverse(int), frac})

# --- rounding ---

# the first `nn` fraction digits, 0s past the last, and the digits dropped
def pad(nn: Nat, right: String) -> String & String:
  match nn:
    case 0n:
      ("", right)
    case 1n+m:
      match right:
        case SNil{}:
          cut.put('0', pad(m, ""))
        case SCon{hd, tl}:
          cut.put(hd, pad(m, tl))

# a 0 digit leaves the answer to the rest; any other digit is nonzero
def nonzero.at(zero: Bool, more: Unit -> Bool) -> Bool:
  match zero:
    case False{}:
      True{}
    case True{}:
      more(Unit{})

# whether any digit is not 0
def nonzero(txt: String) -> Bool:
  match txt:
    case SNil{}:
      False{}
    case SCon{hd, +tl}:
      nonzero.at(Char.is_eq(hd, '0'), _u => nonzero(tl))

# whether the last kept digit is odd; no digit is an even 0
def odd(kept: String) -> Bool:
  match kept:
    case SNil{}:
      False{}
    case SCon{hd, _tl}:
      U32.is_eq(U32.mod(Char.to_u32(hd), 2), 1)

# a first dropped digit of 5 with no other nonzero digit dropped is a tie,
# which goes to the even neighbour
def tie(sticky: Bool, kept: String) -> Bool:
  match sticky:
    case True{}:
      True{}
    case False{}:
      odd(kept)

# the first dropped digit against 5
def round.at(order: Cmp, rest: String, kept: String) -> Bool:
  match order:
    case LT{}:
      False{}
    case EQ{}:
      tie(nonzero(rest), kept)
    case GT{}:
      True{}

# whether the kept digits (last first) go up by one, from the dropped ones
def round.up(dropped: String, kept: String) -> Bool:
  match dropped:
    case SNil{}:
      False{}
    case SCon{hd, rest}:
      round.at(U32.cmp(Char.to_u32(hd), 53), rest, kept)

# one more on a digit, carried: a 9 is 0 and carries
def inc.at(nine: Bool, ch: Char, tl: String, more: Unit -> String) -> String:
  match nine:
    case True{}:
      SCon{'0', more(Unit{})}
    case False{}:
      SCon{Char.from_u32(U32.add(Char.to_u32(ch), 1)), tl}

# one more on digits written last first
def inc(digits: String) -> String:
  match digits:
    case SNil{}:
      "1"
    case SCon{+hd, +tl}:
      inc.at(Char.is_eq(hd, '9'), hd, tl, _u => inc(tl))

# the kept digits, one more when they round up
def bump(go_up: Bool, kept: String) -> String:
  match go_up:
    case True{}:
      inc(kept)
    case False{}:
      kept

# the kept digits split at the last place
def round.keep(+left: String, pair: String & String) -> String:
  (kept, dropped) = pair
  +all = String.reverse.go(kept, left)
  bump(round.up(dropped, all), all)

# every digit to the last kept place, last first, rounded half to even
def round(+nn: Nat, dec: Dec) -> String:
  match dec:
    case Dec{+left, right}:
      round.keep(left, pad(nn, right))

# --- writing ---

# an integer part with its leading 0s dropped; no digit is 0
def trim.at(zero: Bool, ch: Char, tl: String, more: Unit -> String) -> String:
  match zero:
    case True{}:
      more(Unit{})
    case False{}:
      SCon{ch, tl}

# an integer part with its leading 0s dropped; no digit is 0
def trim(int: String) -> String:
  match int:
    case SNil{}:
      "0"
    case SCon{+hd, +tl}:
      trim.at(Char.is_eq(hd, '0'), hd, tl, _u => trim(tl))

# the integer part, then a point and the fraction when there is one
def point(nn: Nat, int: String, frac: String) -> String:
  match nn:
    case 0n:
      int
    case 1n+_m:
      int ++ "." ++ frac

# rounded digits, last first, written with `nn` decimals
def write(+nn: Nat, +digits: String) -> String:
  point(nn, trim(String.reverse(String.drop(digits, nn))),
    String.reverse(String.take(digits, nn)))

# an unsigned number's text with `nn` decimals
def unsigned(txt: String, +nn: Nat) -> String:
  write(nn, round(nn, place(parts(txt))))

# a sign kept in front of the unsigned rest
def text.at(minus: Bool, ch: Char, tl: String, +nn: Nat) -> String:
  match minus:
    case True{}:
      "-" ++ unsigned(tl, nn)
    case False{}:
      unsigned(SCon{ch, tl}, nn)

# a number's text with `nn` decimals
def text(txt: String, +nn: Nat) -> String:
  match txt:
    case SNil{}:
      unsigned("", nn)
    case SCon{+hd, tl}:
      text.at(Char.is_eq(hd, '-'), hd, tl, nn)

# Some of the text with `nn` decimals when `ok`, else None
def fixed.go(ok: Bool, raw: String, +nn: Nat) -> Maybe<&2, String>:
  match ok:
    case True{}:
      Some{text(raw, nn)}
    case False{}:
      None{}

# a JSON number's text with `nn` decimals, or None when it is not one
def fixed(+raw: String, +nn: Nat) -> Maybe<&2, String>:
  fixed.go(V.num.ok(raw), raw, nn)
