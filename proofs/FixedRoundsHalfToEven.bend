# proofs of laws/FixedRoundsHalfToEven.bend
import Base
import ../src/fixed.bend as F
import ../laws/FixedRoundsHalfToEven.bend as Laws

def Laws.round_cut(nn, left, right, kept, dropped, h):
  %Equal.sym(String & String, F.pad(nn, right), (kept, dropped), h)
    : {F.round.keep(left, _)
      == F.bump(F.round.up(dropped, String.reverse.go(kept, left)),
        String.reverse.go(kept, left)) : String}
  {==}

# a character put before a pair's first is the first's head
law fx_put_fst:
  for +ch: Char
  for pp: String & String
  {Pair.fst(String, String, F.cut.put(ch, pp))
    == SCon{ch, Pair.fst(String, String, pp)} : String}

def fx_put_fst(_ch, pp):
  match pp:
    case (_a, _b):
      {==}

def Laws.pad_width(nn, right):
  match nn:
    case 0n:
      {==}
    case 1n+mm:
      match right:
        case SNil{}:
          Equal.trans(Nat,
            String.length(Pair.fst(String, String, F.cut.put('0', F.pad(mm, "")))),
            1n+String.length(Pair.fst(String, String, F.pad(mm, ""))),
            1n+mm,
            Equal.cong(String, Nat, ss => String.length(ss),
              Pair.fst(String, String, F.cut.put('0', F.pad(mm, ""))),
              SCon{'0', Pair.fst(String, String, F.pad(mm, ""))},
              fx_put_fst('0', F.pad(mm, ""))),
            Equal.cong(Nat, Nat, kk => 1n+kk,
              String.length(Pair.fst(String, String, F.pad(mm, ""))), mm,
              Laws.pad_width(mm, "")))
        case SCon{+cc, +tl}:
          Equal.trans(Nat,
            String.length(Pair.fst(String, String, F.cut.put(cc, F.pad(mm, tl)))),
            1n+String.length(Pair.fst(String, String, F.pad(mm, tl))),
            1n+mm,
            Equal.cong(String, Nat, ss => String.length(ss),
              Pair.fst(String, String, F.cut.put(cc, F.pad(mm, tl))),
              SCon{cc, Pair.fst(String, String, F.pad(mm, tl))},
              fx_put_fst(cc, F.pad(mm, tl))),
            Equal.cong(Nat, Nat, kk => 1n+kk,
              String.length(Pair.fst(String, String, F.pad(mm, tl))), mm,
              Laws.pad_width(mm, tl)))

def Laws.pad_none(_right):
  {==}

def Laws.pad_digit(_mm, _ch, _tl):
  {==}

def Laws.pad_past(_mm):
  {==}

def Laws.up_exact(_kept):
  {==}

def Laws.up_below(dd, rest, kept, h):
  %Equal.sym(Cmp, Laws.vs5(dd), LT{}, h)
    : {F.round.at(_, rest, kept) == False{} : Bool}
  {==}

def Laws.up_above(dd, rest, kept, h):
  %Equal.sym(Cmp, Laws.vs5(dd), GT{}, h)
    : {F.round.at(_, rest, kept) == True{} : Bool}
  {==}

def Laws.up_past_half(dd, rest, kept, h_d, h_r):
  %Equal.sym(Cmp, Laws.vs5(dd), EQ{}, h_d)
    : {F.round.at(_, rest, kept) == True{} : Bool}
  %Equal.sym(Bool, F.nonzero(rest), True{}, h_r)
    : {F.tie(_, kept) == True{} : Bool}
  {==}

def Laws.up_tie(dd, rest, last, kept, h_d, h_r):
  %Equal.sym(Cmp, Laws.vs5(dd), EQ{}, h_d)
    : {F.round.at(_, rest, SCon{last, kept})
      == U32.is_eq(U32.mod(Char.to_u32(last), 2), 1) : Bool}
  %Equal.sym(Bool, F.nonzero(rest), False{}, h_r)
    : {F.tie(_, SCon{last, kept})
      == U32.is_eq(U32.mod(Char.to_u32(last), 2), 1) : Bool}
  {==}

def Laws.up_tie_none(dd, rest, h_d, h_r):
  %Equal.sym(Cmp, Laws.vs5(dd), EQ{}, h_d)
    : {F.round.at(_, rest, "") == False{} : Bool}
  %Equal.sym(Bool, F.nonzero(rest), False{}, h_r)
    : {F.tie(_, "") == False{} : Bool}
  {==}

def Laws.nonzero_zeros(kk):
  match kk:
    case 0n:
      {==}
    case 1n+jj:
      Laws.nonzero_zeros(jj)

# a nonzero step whose rest is true is true
law fx_at_true:
  for +zero: Bool
  for more: Unit -> Bool
  for h: {more(Unit{}) == True{} : Bool}
  {F.nonzero.at(zero, more) == True{} : Bool}

def fx_at_true(zero, _more, h):
  match zero:
    case False{}:
      {==}
    case True{}:
      h

def Laws.nonzero_digit(pre, ch, post, h):
  match pre:
    case SNil{}:
      %Equal.sym(Bool, Char.is_eq(ch, '0'), False{}, h)
        : {F.nonzero.at(_, _u => F.nonzero(post)) == True{} : Bool}
      {==}
    case SCon{+cc, +tl}:
      fx_at_true(Char.is_eq(cc, '0'), _u => F.nonzero(tl ++ SCon{ch, post}),
        Laws.nonzero_digit(tl, ch, post, h))

def Laws.bump_up(_kept):
  {==}

def Laws.bump_down(_kept):
  {==}

def Laws.inc_digit(ch, tl, h):
  %Equal.sym(Bool, Char.is_eq(ch, '9'), False{}, h)
    : {F.inc.at(_, ch, tl, _u => F.inc(tl))
      == SCon{Char.from_u32(U32.add(Char.to_u32(ch), 1)), tl} : String}
  {==}

def Laws.inc_nine(_tl):
  {==}

def Laws.inc_nines(kk):
  match kk:
    case 0n:
      {==}
    case 1n+jj:
      Equal.cong(String, String, ss => SCon{'0', ss},
        F.inc(String.repeat("9", jj)), String.repeat("0", jj) ++ "1",
        Laws.inc_nines(jj))
