# get's key search, read over owned keys
import Base
import ../../src/value.bend as V
import ../../laws/SpansReadAsOwned.bend as L1
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ./ArrayLength.bend as M1

# laws/SpansReadAsOwned.bend: the readers do not see spans

# a comparison that has missed stays missed
law find_miss:
  for +aa: String
  for +bb: String
  {V.find.eq.go(aa, bb, False{}) == False{} : Bool}

def find_miss(aa, bb):
  match aa bb:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{_y, _ys}:
      {==}
    case SCon{_x, _xs} SNil{}:
      {==}
    case SCon{_x, _xs} SCon{_y, _ys}:
      {==}

# find_str_eq, one character on, with its comparison named
law find_str_at:
  for cc: Cmp
  for +as: String
  for +bs: String
  for ih: {V.find.eq.go(as, bs, True{}) == String.eq(as, bs) : Bool}
  {V.find.eq.go(as, bs, Cmp.is_eq(cc)) == Cmp.is_eq(String.order.go(as, bs, cc)) : Bool}

def find_str_at(cc, as, bs, ih):
  match cc:
    case LT{}:
      Equal.trans(Bool, V.find.eq.go(as, bs, False{}), False{}, Cmp.is_eq(String.order.go(as, bs, LT{})),
        find_miss(as, bs),
        Equal.sym(Bool, Cmp.is_eq(String.order.go(as, bs, LT{})), False{}, M1.order_go_ne_eq(as, bs, LT{}, {==})))
    case GT{}:
      Equal.trans(Bool, V.find.eq.go(as, bs, False{}), False{}, Cmp.is_eq(String.order.go(as, bs, GT{})),
        find_miss(as, bs),
        Equal.sym(Bool, Cmp.is_eq(String.order.go(as, bs, GT{})), False{}, M1.order_go_ne_eq(as, bs, GT{}, {==})))
    case EQ{}:
      ih

# find.eq is String.eq
law find_str_eq:
  for +aa: String
  for +bb: String
  {V.find.eq.go(aa, bb, True{}) == String.eq(aa, bb) : Bool}

def find_str_eq(aa, bb):
  match aa bb:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{_y, _ys}:
      {==}
    case SCon{_x, _xs} SNil{}:
      {==}
    case SCon{Chr{+xx}, +as} SCon{Chr{+yy}, +bs}:
      find_str_at(U32.cmp(xx, yy), as, bs, find_str_eq(as, bs))

# comparing a span key is comparing the key it covers
law span_find:
  for +src: String
  for +nn: U32
  for +key: String
  {V.span.eq(src, nn, key) == V.find.eq(V.span.str(src, nn, U32.is_zero(nn)), key) : Bool}

def span_find(src, nn, key):
  Equal.trans(Bool, V.span.eq(src, nn, key), String.eq(V.span.str(src, nn, U32.is_zero(nn)), key),
    V.find.eq(V.span.str(src, nn, U32.is_zero(nn)), key), M1.span_eq_go(src, U32.is_zero(nn), key, nn),
    Equal.sym(Bool, V.find.eq(V.span.str(src, nn, U32.is_zero(nn)), key), String.eq(V.span.str(src, nn,
      U32.is_zero(nn)),
      key), find_str_eq(V.span.str(src, nn, U32.is_zero(nn)), key)))

# the rest of a key search, owned
law find_at_own:
  for +rest: V.Json
  for +key: String
  for eq: Bool
  for +vv: V.Json
  {D1.own(V.find.at(rest, key, eq, vv)) == V.find.at(D1.own(rest), key, eq, D1.own(vv)) : V.Json}

def find_at_own(rest, key, eq, _vv):
  match rest:
    case V.JNull{}:
      match eq:
        case True{}:
          {==}
        case False{}:
          {==}
    case V.JBool{+x1}:
      match eq:
        case True{}:
          {==}
        case False{}:
          {==}
    case V.JNum{+x1}:
      match eq:
        case True{}:
          {==}
        case False{}:
          {==}
    case V.JStr{+x1}:
      match eq:
        case True{}:
          {==}
        case False{}:
          {==}
    case V.JArr{+x1}:
      match eq:
        case True{}:
          {==}
        case False{}:
          {==}
    case V.JObj{+x1}:
      match eq:
        case True{}:
          {==}
        case False{}:
          {==}
    case V.JNil{}:
      match eq:
        case True{}:
          {==}
        case False{}:
          {==}
    case V.JCons{+x1, +x2}:
      match eq:
        case True{}:
          {==}
        case False{}:
          {==}
    case V.JPair{+x1, +x2, +x3}:
      match eq:
        case True{}:
          {==}
        case False{}:
          find_at_own(x3, key, V.find.eq(x1, key), x2)
    case V.JSpan{+x1, +x2}:
      match eq:
        case True{}:
          {==}
        case False{}:
          {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      match eq:
        case True{}:
          {==}
        case False{}:
          Equal.trans(V.Json, D1.own(V.find.at(x4, key, V.span.eq(x1, x2, key), x3)),
            V.find.at(D1.own(x4), key, V.span.eq(x1, x2, key), D1.own(x3)),
            V.find.at(D1.own(x4), key, V.find.eq(V.span.str(x1, x2, U32.is_zero(x2)), key), D1.own(x3)),
            find_at_own(x4, key, V.span.eq(x1, x2, key), x3),
            Equal.cong(Bool, V.Json, zz => V.find.at(D1.own(x4), key, zz, D1.own(x3)), V.span.eq(x1, x2, key),
              V.find.eq(V.span.str(x1, x2, U32.is_zero(x2)), key), span_find(x1, x2, key)))

# a key search, owned
law find_own:
  for +cells: V.Json
  for +key: String
  {D1.own(V.find(cells, key)) == V.find(D1.own(cells), key) : V.Json}

def find_own(cells, key):
  match cells:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      {==}
    case V.JObj{+x1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      {==}
    case V.JPair{+x1, +x2, +x3}:
      find_at_own(x3, key, V.find.eq(x1, key), x2)
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      Equal.trans(V.Json, D1.own(V.find.at(x4, key, V.span.eq(x1, x2, key), x3)),
        V.find.at(D1.own(x4), key, V.span.eq(x1, x2, key), D1.own(x3)),
        V.find.at(D1.own(x4), key, V.find.eq(V.span.str(x1, x2, U32.is_zero(x2)), key), D1.own(x3)),
        find_at_own(x4, key, V.span.eq(x1, x2, key), x3),
        Equal.cong(Bool, V.Json, zz => V.find.at(D1.own(x4), key, zz, D1.own(x3)), V.span.eq(x1, x2, key),
          V.find.eq(V.span.str(x1, x2, U32.is_zero(x2)), key), span_find(x1, x2, key)))

def L1.get_same(val, key):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      {==}
    case V.JObj{+x1}:
      find_own(x1, key)
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      {==}
    case V.JPair{+x1, +x2, +x3}:
      {==}
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      {==}
