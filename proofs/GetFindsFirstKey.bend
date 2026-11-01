# proofs of laws/GetFindsFirstKey.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../laws/GetFindsFirstKey.bend as Laws
import ./lemmas/ArrayLength.bend as M1
import ./lemmas/WellFormedCells.bend as M2

def Laws.get_not_obj(val, key, h_kind):
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
    case V.JObj{ps}:
      Empty.absurd({Ezjson.get(V.JObj{ps}, key) == Ezjson.null() : V.Json},
        M1.true_false(h_kind))
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

def Laws.get_empty(_key):
  {==}

# a key that matched: its value, whatever pairs follow
law get_hit.rest:
  for ps: List<&1, String & V.Json>
  for +key: String
  for vv: V.Json
  {V.find.at(V.obj.go(ps), key, True{}, vv) == vv : V.Json}

def get_hit.rest(ps, _key, _vv):
  match ps:
    case Nil{}:
      {==}
    case (_k3, _v3) <> _tl:
      {==}

def Laws.get_hit(k2, vv, ps, key, h_eq):
  ek = Equal.sym(String, k2, key, h_eq)
  %ek : {V.find.at(V.obj.go(ps), key, V.find.eq.go(_, key, True{}), vv) == vv : V.Json}
  rf = Equal.sym(Bool, V.find.eq.go(key, key, True{}), True{}, M2.find_eq_refl(key))
  %rf : {V.find.at(V.obj.go(ps), key, _, vv) == vv : V.Json}
  get_hit.rest(ps, key, vv)

# a key that missed: the rest of the pairs answer, as get on them would
law get_miss.rest:
  for ps: List<&1, String & V.Json>
  for +key: String
  for vv: V.Json
  {V.find.at(V.obj.go(ps), key, False{}, vv) == Ezjson.get(Ezjson.obj(ps), key) : V.Json}

def get_miss.rest(ps, _key, _vv):
  match ps:
    case Nil{}:
      {==}
    case (_k3, _v3) <> _tl:
      {==}

def Laws.get_miss(k2, vv, ps, key, h_ne):
  nf = Equal.sym(Bool, V.find.eq.go(k2, key, True{}), False{}, M2.find_eq_false(k2, key, h_ne))
  %nf : {V.find.at(V.obj.go(ps), key, _, vv) == Ezjson.get(Ezjson.obj(ps), key) : V.Json}
  get_miss.rest(ps, key, vv)
