# len over arrays, and the parser's order on a value's tokens
import Base
import ../../src/value.bend as V
import ../../laws/LenCountsItems.bend as L1
import ../../laws/defs/GrammarDerivations.bend as D1

# Unit for True, Empty for False: tells them apart
def true_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Empty
    case True{}:
      Unit

# True is never False
law true_false:
  for e: {True{} == False{} : Bool}
  Empty

def true_false(e):
  %e : true_ty(_)
  Unit{}

# len.go counts the cells arr.go builds
law len_arr_go:
  for xs: List<&2, V.Json>
  {V.len.go(V.arr.go(xs)) == List.length(&2, V.Json, xs) : Nat}

def len_arr_go(xs):
  match xs:
    case Nil{}:
      {==}
    case hd <> tl:
      %len_arr_go(tl) : {1n+V.len.go(V.arr.go(tl)) == 1n+_ : Nat}
      {==}

def L1.len_arr(xs):
  %len_arr_go(xs) : {U32.from_nat(V.len.go(V.arr.go(xs))) == U32.from_nat(_) : U32}
  {==}

# WP-P1: the parser on a value's tokens

# a string walk whose first characters already differ answers that order
law order_go_ne:
  for +aa: String
  for +bb: String
  for cc: Cmp
  for ne: {Cmp.is_eq(cc) == False{} : Bool}
  {String.order.go(aa, bb, cc) == cc : Cmp}

def order_go_ne(aa, bb, cc, ne):
  match aa bb:
    case SNil{} SNil{}:
      match cc:
        case LT{}:
          {==}
        case GT{}:
          {==}
        case EQ{}:
          Empty.absurd({String.order.go(SNil{}, SNil{}, EQ{}) == EQ{} : Cmp}, true_false(ne))
    case SNil{} SCon{y, ys}:
      match cc:
        case LT{}:
          {==}
        case GT{}:
          {==}
        case EQ{}:
          Empty.absurd({String.order.go(SNil{}, SCon{y, ys}, EQ{}) == EQ{} : Cmp}, true_false(ne))
    case SCon{x, xs} SNil{}:
      match cc:
        case LT{}:
          {==}
        case GT{}:
          {==}
        case EQ{}:
          Empty.absurd({String.order.go(SCon{x, xs}, SNil{}, EQ{}) == EQ{} : Cmp}, true_false(ne))
    case SCon{Chr{x}, xs} SCon{Chr{y}, ys}:
      match cc:
        case LT{}:
          {==}
        case GT{}:
          {==}
        case EQ{}:
          Empty.absurd({String.order.go(SCon{Chr{x}, xs}, SCon{Chr{y}, ys}, EQ{}) == EQ{} : Cmp}, true_false(ne))

# so String.eq of such a walk is False
law order_go_ne_eq:
  for +aa: String
  for +bb: String
  for cc: Cmp
  for +ne: {Cmp.is_eq(cc) == False{} : Bool}
  {Cmp.is_eq(String.order.go(aa, bb, cc)) == False{} : Bool}

def order_go_ne_eq(aa, bb, cc, ne):
  Equal.trans(Bool, Cmp.is_eq(String.order.go(aa, bb, cc)), Cmp.is_eq(cc), False{},
    Equal.cong(Cmp, Bool, zz => Cmp.is_eq(zz), String.order.go(aa, bb, cc), cc, order_go_ne(aa, bb, cc, ne)), ne)

# WP-H: parse on spans against parse on what they cover

# a span comparison that has missed stays missed
law span_miss:
  for +src: String
  for +zero: Bool
  for +key: String
  for +nn: U32
  {V.span.eq.go(src, False{}, zero, key, nn) == False{} : Bool}

def span_miss(src, _zero, _key, _nn):
  match src:
    case SNil{}:
      {==}
    case SCon{_a, _as}:
      {==}

# span_eq_go, one character on, with its comparison named
law span_eq_at:
  for cc: Cmp
  for +as: String
  for +bs: String
  for +nn: U32
  for ih: {V.span.eq.go(as, True{}, U32.is_zero(U32.sub(nn, 1)), bs, U32.sub(nn, 1)) ==
    String.eq(V.span.str(as, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1))), bs) : Bool}
  {V.span.eq.go(as, Cmp.is_eq(cc), U32.is_zero(U32.sub(nn, 1)), bs, U32.sub(nn, 1)) ==
    Cmp.is_eq(String.order.go(V.span.str(as, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1))), bs, cc)) : Bool}

def span_eq_at(cc, as, bs, nn, ih):
  match cc:
    case LT{}:
      +sp = V.span.str(as, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)))
      Equal.trans(Bool, V.span.eq.go(as, False{}, U32.is_zero(U32.sub(nn, 1)), bs, U32.sub(nn, 1)), False{},
        Cmp.is_eq(String.order.go(sp, bs, LT{})),
        span_miss(as, U32.is_zero(U32.sub(nn, 1)), bs, U32.sub(nn, 1)),
        Equal.sym(Bool, Cmp.is_eq(String.order.go(sp, bs, LT{})), False{}, order_go_ne_eq(sp, bs, LT{}, {==})))
    case GT{}:
      +sp = V.span.str(as, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)))
      Equal.trans(Bool, V.span.eq.go(as, False{}, U32.is_zero(U32.sub(nn, 1)), bs, U32.sub(nn, 1)), False{},
        Cmp.is_eq(String.order.go(sp, bs, GT{})),
        span_miss(as, U32.is_zero(U32.sub(nn, 1)), bs, U32.sub(nn, 1)),
        Equal.sym(Bool, Cmp.is_eq(String.order.go(sp, bs, GT{})), False{}, order_go_ne_eq(sp, bs, GT{}, {==})))
    case EQ{}:
      ih

# comparing a span with a key is comparing what the span covers with it
law span_eq_go:
  for +src: String
  for +zero: Bool
  for +key: String
  for +nn: U32
  {V.span.eq.go(src, True{}, zero, key, nn) == String.eq(V.span.str(src, nn, zero), key) : Bool}

def span_eq_go(src, zero, key, nn):
  match src:
    case SNil{}:
      match zero:
        case True{}:
          match key:
            case SNil{}:
              {==}
            case SCon{_b, _bs}:
              {==}
        case False{}:
          match key:
            case SNil{}:
              {==}
            case SCon{_b, _bs}:
              {==}
    case SCon{Chr{+xx}, +as}:
      match zero:
        case True{}:
          match key:
            case SNil{}:
              {==}
            case SCon{_b, _bs}:
              {==}
        case False{}:
          match key:
            case SNil{}:
              {==}
            case SCon{Chr{+yy}, +bs}:
              span_eq_at(U32.cmp(xx, yy), as, bs, nn,
                span_eq_go(as, U32.is_zero(U32.sub(nn, 1)), bs, U32.sub(nn, 1)))

# pieces spelled in front of a tail
def sp(ps: List<&2, D1.Piece>, tail: String) -> String:
  match ps:
    case Nil{}:
      tail
    case pc <> tl:
      D1.piece.text(pc) ++ sp(tl, tail)
