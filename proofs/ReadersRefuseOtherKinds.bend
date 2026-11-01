# proofs of laws/ReadersRefuseOtherKinds.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../laws/ReadersRefuseOtherKinds.bend as Laws
import ./lemmas/ArrayLength.bend as M1

def Laws.as_bool_kind(val):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{_}:
      {==}
    case V.JNum{_}:
      {==}
    case V.JStr{_}:
      {==}
    case V.JArr{_}:
      {==}
    case V.JObj{_}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{_, _}:
      {==}
    case V.JPair{_, _, _}:
      {==}
    case V.JSpan{_, _}:
      {==}
    case V.JBind{_, _, _, _}:
      {==}

def Laws.as_str_kind(val):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{_}:
      {==}
    case V.JNum{_}:
      {==}
    case V.JStr{_}:
      {==}
    case V.JArr{_}:
      {==}
    case V.JObj{_}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{_, _}:
      {==}
    case V.JPair{_, _, _}:
      {==}
    case V.JSpan{_, _}:
      {==}
    case V.JBind{_, _, _, _}:
      {==}

def Laws.as_num_kind(val):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{_}:
      {==}
    case V.JNum{_}:
      {==}
    case V.JStr{_}:
      {==}
    case V.JArr{_}:
      {==}
    case V.JObj{_}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{_, _}:
      {==}
    case V.JPair{_, _, _}:
      {==}
    case V.JSpan{_, _}:
      {==}
    case V.JBind{_, _, _, _}:
      {==}

def Laws.as_u32_kind(val, h_kind):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{_}:
      {==}
    case V.JNum{raw}:
      Empty.absurd({Ezjson.as_u32(V.JNum{raw}) == None{} : Maybe<&2, U32>},
        M1.true_false(h_kind))
    case V.JStr{_}:
      {==}
    case V.JArr{_}:
      {==}
    case V.JObj{_}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{_, _}:
      {==}
    case V.JPair{_, _, _}:
      {==}
    case V.JSpan{_, _}:
      {==}
    case V.JBind{_, _, _, _}:
      {==}

def Laws.as_f32_kind(val, h_kind):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{_}:
      {==}
    case V.JNum{raw}:
      Empty.absurd({Ezjson.as_f32(V.JNum{raw}) == None{} : Maybe<&2, F32>},
        M1.true_false(h_kind))
    case V.JStr{_}:
      {==}
    case V.JArr{_}:
      {==}
    case V.JObj{_}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{_, _}:
      {==}
    case V.JPair{_, _, _}:
      {==}
    case V.JSpan{_, _}:
      {==}
    case V.JBind{_, _, _, _}:
      {==}
