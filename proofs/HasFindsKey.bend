# proofs of laws/HasFindsKey.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../src/lazy.bend as Lazy
import ../laws/HasFindsKey.bend as Laws
import ./lemmas/ArrayLength.bend as M1
import ./lemmas/WellFormedCells.bend as M2

def Laws.has_not_obj(val, key, h_kind):
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
      Empty.absurd({Ezjson.has(V.JObj{ps}, key) == False{} : Bool},
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

def Laws.has_empty(_key):
  {==}

def Laws.has_hit(k2, _vv, ps, key, h_eq):
  ek = Equal.sym(String, k2, key, h_eq)
  %ek : {Lazy.stop(Bool, V.find.eq.go(_, key, True{}), True{}, _u => V.has.go(V.obj.go(ps), key)) == True{} : Bool}
  rf = Equal.sym(Bool, V.find.eq.go(key, key, True{}), True{}, M2.find_eq_refl(key))
  %rf : {Lazy.stop(Bool, _, True{}, _u => V.has.go(V.obj.go(ps), key)) == True{} : Bool}
  {==}

def Laws.has_miss(k2, _vv, ps, key, h_ne):
  nf = Equal.sym(Bool, V.find.eq.go(k2, key, True{}), False{}, M2.find_eq_false(k2, key, h_ne))
  %nf : {Lazy.stop(Bool, _, True{}, _u => V.has.go(V.obj.go(ps), key)) == Ezjson.has(Ezjson.obj(ps), key) : Bool}
  {==}
