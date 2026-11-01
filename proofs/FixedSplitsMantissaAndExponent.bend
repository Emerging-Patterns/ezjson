# proofs of laws/FixedSplitsMantissaAndExponent.bend
import Base
import ../src/fixed.bend as F
import ../laws/FixedSplitsMantissaAndExponent.bend as Laws
import ../laws/defs/CursorAndNumberRules.bend as D1
import ./lemmas/LexemeOrder.bend as M1

# --- fixed decimals (JSON-FIX) ---

# a true `when` with a false yes: its test is false
law fx_when_test:
  for +cc: Bool
  for +rest: Bool
  for +h: {D1.when(cc, False{}, rest) == True{} : Bool}
  {cc == False{} : Bool}

def fx_when_test(cc, _rest, h):
  match cc:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, M1.false_true(h))
    case False{}:
      {==}

# a true `when` with a false yes: its no is true
law fx_when_rest:
  for +cc: Bool
  for +rest: Bool
  for +h: {D1.when(cc, False{}, rest) == True{} : Bool}
  {rest == True{} : Bool}

def fx_when_rest(cc, _rest, h):
  match cc:
    case True{}:
      Empty.absurd({_rest == True{} : Bool}, M1.false_true(h))
    case False{}:
      h

# a text with no exponent mark, then a mark: the cut is at that mark
law fx_cut_e_hit:
  for +aa: String
  for +ch: Char
  for +bb: String
  for +h_a: {Laws.no_e(aa) == True{} : Bool}
  for +h_c: {F.mark.e(ch) == True{} : Bool}
  {F.cut.e(aa ++ SCon{ch, bb}) == (aa, bb) : String & String}

def fx_cut_e_hit(aa, ch, bb, h_a, h_c):
  match aa:
    case SNil{}:
      %Equal.sym(Bool, F.mark.e(ch), True{}, h_c)
        : {F.cut.at(_, ch, bb, _u => F.cut.e(bb)) == ("", bb) : String & String}
      {==}
    case SCon{+cc, +tl}:
      %Equal.sym(Bool, F.mark.e(cc), False{},
        fx_when_test(F.mark.e(cc), Laws.no_e(tl), h_a))
        : {F.cut.at(_, cc, tl ++ SCon{ch, bb}, _u => F.cut.e(tl ++ SCon{ch, bb}))
          == (SCon{cc, tl}, bb) : String & String}
      Equal.cong(String & String, String & String, pp => F.cut.put(cc, pp),
        F.cut.e(tl ++ SCon{ch, bb}), (tl, bb),
        fx_cut_e_hit(tl, ch, bb, fx_when_rest(F.mark.e(cc), Laws.no_e(tl), h_a),
          h_c))

# a text with no exponent mark is not cut
law fx_cut_e_none:
  for +aa: String
  for +h_a: {Laws.no_e(aa) == True{} : Bool}
  {F.cut.e(aa) == (aa, "") : String & String}

def fx_cut_e_none(aa, h_a):
  match aa:
    case SNil{}:
      {==}
    case SCon{+cc, +tl}:
      %Equal.sym(Bool, F.mark.e(cc), False{},
        fx_when_test(F.mark.e(cc), Laws.no_e(tl), h_a))
        : {F.cut.at(_, cc, tl, _u => F.cut.e(tl)) == (SCon{cc, tl}, "")
          : String & String}
      Equal.cong(String & String, String & String, pp => F.cut.put(cc, pp),
        F.cut.e(tl), (tl, ""),
        fx_cut_e_none(tl, fx_when_rest(F.mark.e(cc), Laws.no_e(tl), h_a)))

# a text with no point, then a point: the cut is at that point
law fx_cut_dot_hit:
  for +aa: String
  for +bb: String
  for +h_a: {Laws.no_dot(aa) == True{} : Bool}
  {F.cut.dot(aa ++ SCon{'.', bb}) == (aa, bb) : String & String}

def fx_cut_dot_hit(aa, bb, h_a):
  match aa:
    case SNil{}:
      {==}
    case SCon{+cc, +tl}:
      %Equal.sym(Bool, F.mark.dot(cc), False{},
        fx_when_test(F.mark.dot(cc), Laws.no_dot(tl), h_a))
        : {F.cut.at(_, cc, tl ++ SCon{'.', bb}, _u => F.cut.dot(tl ++ SCon{'.', bb}))
          == (SCon{cc, tl}, bb) : String & String}
      Equal.cong(String & String, String & String, pp => F.cut.put(cc, pp),
        F.cut.dot(tl ++ SCon{'.', bb}), (tl, bb),
        fx_cut_dot_hit(tl, bb, fx_when_rest(F.mark.dot(cc), Laws.no_dot(tl), h_a)))

# a text with no point is not cut
law fx_cut_dot_none:
  for +aa: String
  for +h_a: {Laws.no_dot(aa) == True{} : Bool}
  {F.cut.dot(aa) == (aa, "") : String & String}

def fx_cut_dot_none(aa, h_a):
  match aa:
    case SNil{}:
      {==}
    case SCon{+cc, +tl}:
      %Equal.sym(Bool, F.mark.dot(cc), False{},
        fx_when_test(F.mark.dot(cc), Laws.no_dot(tl), h_a))
        : {F.cut.at(_, cc, tl, _u => F.cut.dot(tl)) == (SCon{cc, tl}, "")
          : String & String}
      Equal.cong(String & String, String & String, pp => F.cut.put(cc, pp),
        F.cut.dot(tl), (tl, ""),
        fx_cut_dot_none(tl, fx_when_rest(F.mark.dot(cc), Laws.no_dot(tl), h_a)))

def Laws.unsigned_steps(_txt, _nn):
  {==}

def Laws.parts_exp(mant, ch, exp, h_m, h_c):
  Equal.cong(String & String, (String & String) & (Bool & String),
    pp => F.parts.of(pp), F.cut.e(mant ++ SCon{ch, exp}), (mant, exp),
    fx_cut_e_hit(mant, ch, exp, h_m, h_c))

def Laws.parts_plain(mant, h_m):
  Equal.cong(String & String, (String & String) & (Bool & String),
    pp => F.parts.of(pp), F.cut.e(mant), (mant, ""), fx_cut_e_none(mant, h_m))

def Laws.mant_dot(int, frac, h_i):
  fx_cut_dot_hit(int, frac, h_i)

def Laws.mant_int(int, h_i):
  fx_cut_dot_none(int, h_i)

def Laws.esign_minus(_exp):
  {==}

def Laws.esign_plus(_exp):
  {==}

def Laws.esign_digits(ch, tl, h_m, h_p):
  %Equal.sym(Bool, Char.is_eq(ch, '-'), False{}, h_m)
    : {F.esign.at(_, Char.is_eq(ch, '+'), ch, tl) == (False{}, SCon{ch, tl})
      : Bool & String}
  %Equal.sym(Bool, Char.is_eq(ch, '+'), False{}, h_p)
    : {F.esign.at(False{}, _, ch, tl) == (False{}, SCon{ch, tl})
      : Bool & String}
  {==}

def Laws.place_parts(_int, _frac, _neg, _exp):
  {==}

def Laws.nat_start(_exp):
  {==}

def Laws.nat_end(_acc):
  {==}

def Laws.nat_snoc(exp, ch, acc):
  match exp:
    case SNil{}:
      {==}
    case SCon{+cc, +tl}:
      Laws.nat_snoc(tl, ch, Nat.add(Nat.mul(acc, 10n), F.digit.nat(cc)))

def Laws.move_right(_kk, _dec):
  {==}

def Laws.move_left(_kk, _dec):
  {==}

def Laws.ups_zero(_dec):
  {==}

def Laws.ups_succ(_kk, _dec):
  {==}

def Laws.downs_zero(_dec):
  {==}

def Laws.downs_succ(_kk, _dec):
  {==}

def Laws.up_digit(_left, _ch, _tl):
  {==}

def Laws.up_zero(_left):
  {==}

def Laws.down_digit(_ch, _tl, _right):
  {==}

def Laws.down_zero(_right):
  {==}

def Laws.up_down(_left, _ch, _tl):
  {==}

def Laws.down_up(_ch, _tl, _right):
  {==}
