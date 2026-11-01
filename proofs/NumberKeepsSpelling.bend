# proofs of laws/NumberKeepsSpelling.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../laws/NumberKeepsSpelling.bend as Laws
import ../laws/PrintRoundTrips.bend as L1
import ../laws/ReadersRefuseOtherKinds.bend as L2
import ../laws/defs/CursorAndNumberRules.bend as D1
import ./lemmas/ArrayLength.bend as M1
import ./lemmas/LexemeOrder.bend as M2
import ./lemmas/OwnedParse.bend as M3
import ./lemmas/ParserReadsTokens.bend as M4
import ./lemmas/PrintFix.bend as M5

# a value whose owned form is a number is that number
law own_num:
  for +val: V.Json
  for +raw: String
  for e: {D1.own(val) == V.JNum{raw} : V.Json}
  {val == V.JNum{raw} : V.Json}

def own_num(val, raw, e):
  match val:
    case V.JNull{}:
      Empty.absurd({V.JNull{} == V.JNum{raw} : V.Json}, M2.false_true(Equal.cong(V.Json, Bool, zz => L2.is_num(zz),
        D1.own(V.JNull{}), V.JNum{raw}, e)))
    case V.JBool{+x1}:
      Empty.absurd({V.JBool{x1} == V.JNum{raw} : V.Json}, M2.false_true(Equal.cong(V.Json, Bool, zz => L2.is_num(zz),
        D1.own(V.JBool{x1}), V.JNum{raw}, e)))
    case V.JNum{+x1}:
      e
    case V.JStr{+x1}:
      Empty.absurd({V.JStr{x1} == V.JNum{raw} : V.Json}, M2.false_true(Equal.cong(V.Json, Bool, zz => L2.is_num(zz),
        D1.own(V.JStr{x1}), V.JNum{raw}, e)))
    case V.JArr{+x1}:
      Empty.absurd({V.JArr{x1} == V.JNum{raw} : V.Json}, M2.false_true(Equal.cong(V.Json, Bool, zz => L2.is_num(zz),
        D1.own(V.JArr{x1}), V.JNum{raw}, e)))
    case V.JObj{+x1}:
      Empty.absurd({V.JObj{x1} == V.JNum{raw} : V.Json}, M2.false_true(Equal.cong(V.Json, Bool, zz => L2.is_num(zz),
        D1.own(V.JObj{x1}), V.JNum{raw}, e)))
    case V.JNil{}:
      Empty.absurd({V.JNil{} == V.JNum{raw} : V.Json}, M2.false_true(Equal.cong(V.Json, Bool, zz => L2.is_num(zz),
        D1.own(V.JNil{}), V.JNum{raw}, e)))
    case V.JCons{+x1, +x2}:
      Empty.absurd({V.JCons{x1, x2} == V.JNum{raw} : V.Json}, M2.false_true(Equal.cong(V.Json, Bool,
          zz => L2.is_num(zz),
        D1.own(V.JCons{x1, x2}), V.JNum{raw}, e)))
    case V.JPair{+x1, +x2, +x3}:
      Empty.absurd({V.JPair{x1, x2, x3} == V.JNum{raw} : V.Json}, M2.false_true(Equal.cong(V.Json, Bool,
        zz => L2.is_num(zz),
        D1.own(V.JPair{x1, x2, x3}), V.JNum{raw}, e)))
    case V.JSpan{+x1, +x2}:
      Empty.absurd({V.JSpan{x1, x2} == V.JNum{raw} : V.Json}, M2.false_true(Equal.cong(V.Json, Bool,
          zz => L2.is_num(zz),
        D1.own(V.JSpan{x1, x2}), V.JNum{raw}, e)))
    case V.JBind{+x1, +x2, +x3, +x4}:
      Empty.absurd({V.JBind{x1, x2, x3, x4} == V.JNum{raw} : V.Json}, M2.false_true(Equal.cong(V.Json, Bool,
        zz => L2.is_num(zz),
        D1.own(V.JBind{x1, x2, x3, x4}), V.JNum{raw}, e)))

# a parse result whose owned form is a number is that number
law own_m_num:
  for +mb: Maybe<&2, V.Json>
  for +raw: String
  for e: {D1.own_m(mb) == Some{V.JNum{raw}} : Maybe<&2, V.Json>}
  {mb == Some{V.JNum{raw}} : Maybe<&2, V.Json>}

def own_m_num(mb, raw, e):
  match mb:
    case None{}:
      Empty.absurd({None{} == Some{V.JNum{raw}} : Maybe<&2, V.Json>}, M1.true_false(Equal.cong(Maybe<&2, V.Json>, Bool,
        zz => M3.is_none(zz), None{},
        Some{V.JNum{raw}}, e)))
    case Some{+jj}:
      Equal.cong(V.Json, Maybe<&2, V.Json>, zz => Some{zz}, jj, V.JNum{raw}, own_num(jj, raw,
        Equal.cong(Maybe<&2, V.Json>, V.Json, zz => M4.unsome(zz), Some{D1.own(jj)}, Some{V.JNum{raw}}, e)))

def Laws.parse_num(raw, h_ok, h_s):
  own_m_num(Ezjson.parse(raw), raw, L1.print_parse(V.JNum{raw}, h_ok, h_s))

def Laws.print_num(_raw):
  {==}
