# proofs of laws/EventTextReadsStrings.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../src/pull.bend as Pull
import ../laws/EventTextReadsStrings.bend as Laws
import ../laws/defs/CursorAndNumberRules.bend as D1
import ./lemmas/ArrayLength.bend as M1
import ./lemmas/WordArithmetic.bend as M2

# Some of a span's characters is Some of the first nn characters of its source
law some_span:
  for +src: String
  for +nn: U32
  {Some{V.span.str(src, nn, U32.is_zero(nn))} == Some{D1.take(src, U32.to_nat(nn))} : Maybe<&2, String>}

def some_span(src, nn):
  Equal.cong(String, Maybe<&2, String>, xx => Some{xx}, V.span.str(src, nn, U32.is_zero(nn)),
    D1.take(src, U32.to_nat(nn)), M2.span_take(src, nn))

def Laws.text_str(_body):
  {==}

def Laws.text_key(_body):
  {==}

def Laws.text_str_span(src, nn):
  some_span(src, nn)

def Laws.text_key_span(src, nn):
  some_span(src, nn)

def Laws.text_num(src, nn):
  some_span(src, nn)

def Laws.text_none(ev, h_kind):
  match ev:
    case Pull.ENull{}:
      {==}
    case Pull.EBool{_}:
      {==}
    case Pull.ENum{aa, bb}:
      Empty.absurd({Ezjson.text(Pull.ENum{aa, bb}) == None{} : Maybe<&2, String>}, M1.true_false(h_kind))
    case Pull.EStr{aa}:
      Empty.absurd({Ezjson.text(Pull.EStr{aa}) == None{} : Maybe<&2, String>}, M1.true_false(h_kind))
    case Pull.EStrS{aa, bb}:
      Empty.absurd({Ezjson.text(Pull.EStrS{aa, bb}) == None{} : Maybe<&2, String>}, M1.true_false(h_kind))
    case Pull.EKey{aa}:
      Empty.absurd({Ezjson.text(Pull.EKey{aa}) == None{} : Maybe<&2, String>}, M1.true_false(h_kind))
    case Pull.EKeyS{aa, bb}:
      Empty.absurd({Ezjson.text(Pull.EKeyS{aa, bb}) == None{} : Maybe<&2, String>}, M1.true_false(h_kind))
    case Pull.EBeginArr{}:
      {==}
    case Pull.EEndArr{}:
      {==}
    case Pull.EBeginObj{}:
      {==}
    case Pull.EEndObj{}:
      {==}
    case Pull.EEnd{}:
      {==}
    case Pull.EErr{}:
      {==}
